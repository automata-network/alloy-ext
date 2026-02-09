//! Extended network provider with auto-recovery and nonce lifecycle management.
//!
//! This module provides `NetworkProvider`, an enhanced Ethereum provider that:
//!
//! - **Integrates StatefulNonceManager**: Tracks nonce lifecycle (Reserved → Pending → Confirmed/Abandoned)
//! - **Auto-Recovery**: Automatically handles nonce errors, network timeouts, and gap filling
//! - **Transaction Rebroadcasting**: Periodically resends transactions to prevent mempool eviction
//! - **TrackedPendingTx**: Returns pending transactions with nonce confirmation tracking
//!
//! ## Architecture
//!
//! ```text
//! NetworkProvider (enum)
//! ├── Http: Basic provider without signing (read-only)
//! └── Wallet: Full provider with signing + nonce management
//!
//! Fillers Stack:
//! ├── ChainIdFiller: Sets chain_id
//! ├── GasFiller: Estimates gas
//! ├── BlobGasFiller: Handles EIP-4844 blob gas
//! ├── NonceFiller<StatefulNonceManager>: Assigns + tracks nonces
//! └── WalletFiller<EthereumWallet>: Signs transactions (Wallet variant only)
//! ```
//!
//! ## Usage Flow
//!
//! 1. Create provider: `NetworkProvider::with_http(url, polling, timeout)`
//! 2. Add signer: `provider.with_signer(signer)`
//! 3. Send transaction: `provider.send_transaction_ex(tx).await`
//! 4. Get receipt: `tracked_tx.get_receipt().await` (auto-confirms nonce)

use std::{sync::Arc, time::Duration};

use alloy::{
    consensus::Transaction,
    network::{Ethereum, EthereumWallet, Network, NetworkWallet},
    primitives::{Address, B256},
    providers::{
        fillers::{
            BlobGasFiller, ChainIdFiller, FillProvider, FillerControlFlow, GasFillable, GasFiller,
            JoinFill, NonceFiller, TxFiller, WalletFiller,
        },
        Identity, PendingTransactionBuilder, Provider, ProviderBuilder, RootProvider, SendableTx,
    },
    signers::local::PrivateKeySigner,
    transports::{RpcError, TransportResult},
};

use crate::ext::{
    backoff_duration, classify_rpc_error, pretty_rpc_error, AtomicNonceState, RecoveryOptions,
    RecoveryResult, RpcErrorKind, SingleRecoveryResult, StatefulNonceManager, TrackedPendingTx,
    TxGas,
};

// ============================================================================
// Provider Configuration
// ============================================================================

/// Configuration for transaction rebroadcasting.
///
/// When waiting for a transaction receipt, the provider can periodically
/// rebroadcast the signed transaction to ensure it stays in the mempool
/// and gets propagated to miners/validators.
#[derive(Debug, Clone)]
pub struct RebroadcastConfig {
    /// Enable rebroadcasting (default: true)
    pub enabled: bool,
    /// Interval between rebroadcast attempts (default: 5 seconds)
    pub interval: Duration,
}

impl Default for RebroadcastConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            interval: Duration::from_secs(5),
        }
    }
}

impl RebroadcastConfig {
    /// Create config with rebroadcasting disabled
    pub fn disabled() -> Self {
        Self {
            enabled: false,
            ..Default::default()
        }
    }

    /// Set rebroadcast interval
    pub fn with_interval(mut self, interval: Duration) -> Self {
        self.interval = interval;
        self
    }

    /// Enable or disable rebroadcasting
    pub fn with_enabled(mut self, enabled: bool) -> Self {
        self.enabled = enabled;
        self
    }
}

/// Configuration for automatic cancel fallback on receipt timeout.
///
/// When a transaction times out during the initial wait period (Phase 1),
/// a cancel transaction can be automatically sent with higher gas price.
/// The system then enters Phase 2, racing the original and cancel transactions.
///
/// ## Usage
///
/// ```ignore
/// // get_receipt() returns &TxResolution with cancel fallback behavior
/// let resolution = tracked.get_receipt().await?;
/// match resolution {
///     TxResolution::Confirmed { .. } => { /* Phase 1 success */ }
///     TxResolution::Cancelled { .. } => { /* Cancel won the race */ }
///     TxResolution::Timeout { .. } => { /* Both timed out */ }
///     _ => {}
/// }
/// ```
#[derive(Debug, Clone)]
pub struct CancelConfig {
    pub enabled: bool,
    /// Gas price multiplier for cancel transaction (default: 2.0).
    /// Must be > 1.0 to outbid the original transaction in mempool.
    /// Higher values increase likelihood of cancel being mined first.
    pub gas_multiplier: f64,

    /// Phase 2 timeout multiplier relative to receipt_timeout (default: 5.0).
    /// Phase 2 timeout = receipt_timeout * phase2_timeout_multiplier.
    /// Only used when `phase2_timeout` is None.
    pub phase2_timeout_multiplier: f64,

    /// Explicit Phase 2 timeout duration.
    /// When set, overrides `phase2_timeout_multiplier`.
    pub phase2_timeout: Option<Duration>,
}

impl Default for CancelConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            gas_multiplier: 2.0,
            phase2_timeout_multiplier: 5.0,
            phase2_timeout: None,
        }
    }
}

impl CancelConfig {
    /// Set gas price multiplier for cancel transaction.
    pub fn with_gas_multiplier(mut self, multiplier: f64) -> Self {
        self.gas_multiplier = multiplier;
        self
    }

    /// Set Phase 2 timeout multiplier (relative to receipt_timeout).
    pub fn with_phase2_timeout_multiplier(mut self, multiplier: f64) -> Self {
        self.phase2_timeout_multiplier = multiplier;
        self
    }

    /// Set explicit Phase 2 timeout duration.
    pub fn with_phase2_timeout(mut self, timeout: Duration) -> Self {
        self.phase2_timeout = Some(timeout);
        self
    }
}

/// Configuration for provider behavior including recovery options.
#[derive(Debug, Clone)]
pub struct ProviderConfig {
    /// Enable automatic recovery for nonce errors (default: true)
    pub auto_recovery: bool,
    /// Gas price multiplier for cancel transactions during gap filling (default: 1.1)
    pub recovery_gas_multiplier: f64,
    /// Maximum retry attempts for recoverable errors (default: 3)
    pub max_send_retries: u32,
    /// Base backoff duration in milliseconds for retries (default: 100)
    pub retry_backoff_ms: u64,
    /// Rebroadcast configuration
    pub rebroadcast: RebroadcastConfig,
    /// Cancel fallback configuration for `get_receipt_with_cancel()`
    pub cancel: CancelConfig,
}

impl Default for ProviderConfig {
    fn default() -> Self {
        Self {
            auto_recovery: true,
            recovery_gas_multiplier: 1.1,
            max_send_retries: 3,
            retry_backoff_ms: 100,
            rebroadcast: RebroadcastConfig::default(),
            cancel: CancelConfig::default(),
        }
    }
}

impl ProviderConfig {
    /// Create config with auto_recovery disabled
    pub fn no_recovery() -> Self {
        Self {
            auto_recovery: false,
            ..Default::default()
        }
    }

    /// Set auto_recovery flag
    pub fn with_auto_recovery(mut self, enabled: bool) -> Self {
        self.auto_recovery = enabled;
        self
    }

    /// Set gas multiplier for recovery
    pub fn with_gas_multiplier(mut self, multiplier: f64) -> Self {
        self.recovery_gas_multiplier = multiplier;
        self
    }

    /// Set max retry attempts
    pub fn with_max_retries(mut self, max: u32) -> Self {
        self.max_send_retries = max;
        self
    }

    /// Set rebroadcast configuration
    pub fn with_rebroadcast(mut self, rebroadcast: RebroadcastConfig) -> Self {
        self.rebroadcast = rebroadcast;
        self
    }

    /// Set cancel fallback configuration
    pub fn with_cancel(mut self, cancel: CancelConfig) -> Self {
        self.cancel = cancel;
        self
    }
}

// ============================================================================
// Provider type aliases
// ============================================================================

#[derive(Debug, Clone)]
pub struct BoostGasFiller {
    pub multiplier: u64,
}

impl BoostGasFiller {
    pub fn multiplied(multiplier: u64) -> Self {
        Self { multiplier }
    }
}

impl<N: Network> TxFiller<N> for BoostGasFiller {
    type Fillable = <GasFiller as TxFiller<N>>::Fillable;

    fn status(&self, tx: &<N as Network>::TransactionRequest) -> FillerControlFlow {
        <GasFiller as TxFiller<N>>::status(&GasFiller, tx)
    }

    fn fill_sync(&self, _tx: &mut SendableTx<N>) {}

    async fn prepare<P>(
        &self,
        provider: &P,
        tx: &<N as Network>::TransactionRequest,
    ) -> TransportResult<Self::Fillable>
    where
        P: Provider<N>,
    {
        GasFiller.prepare(provider, tx).await
    }

    async fn fill(
        &self,
        mut fillable: Self::Fillable,
        tx: SendableTx<N>,
    ) -> TransportResult<SendableTx<N>> {
        let gas_limit = match &mut fillable {
            GasFillable::Legacy { gas_limit, .. } => gas_limit,
            GasFillable::Eip1559 { gas_limit, .. } => gas_limit,
        };
        *gas_limit = (*gas_limit * self.multiplier) / 100;
        Ok(GasFiller.fill(fillable, tx).await?)
    }
}

/// Basic provider with gas, blob gas, nonce (StatefulNonceManager), and chain ID fillers
pub type BasicProvider = JoinFill<
    JoinFill<JoinFill<JoinFill<Identity, ChainIdFiller>, BoostGasFiller>, BlobGasFiller>,
    NonceFiller<StatefulNonceManager>,
>;

#[allow(async_fn_in_trait)]
pub trait ProviderEx<N: Network>: Provider<N> + Clone {
    fn get_receipt_timeout(&self) -> Option<Duration>;
    fn nonce_manager(&self) -> &StatefulNonceManager;
    fn config(&self) -> &ProviderConfig;
    fn chain_id(&self) -> u64;

    /// Send a transaction and return TrackedPendingTx with nonce information.
    ///
    /// This method fills the transaction (including nonce), extracts the nonce
    /// and from address, then sends the transaction.
    ///
    /// ## Auto Recovery
    ///
    /// When `auto_recovery` is enabled (default), this method will automatically:
    /// - Sync nonce from chain on `nonce too low` errors
    /// - Recover abandoned nonces on `nonce too high` errors
    /// - Retry with exponential backoff on network errors
    async fn send_transaction_ex(
        &self,
        tx: N::TransactionRequest,
    ) -> TransportResult<TrackedPendingTx<Self, N>>
    where
        Self: Sized;

    async fn send_transaction_inner(
        &self,
        tx: SendableTx<N>,
    ) -> TransportResult<PendingTransactionBuilder<N>>;

    /// Fill a transaction request with gas, nonce, chain_id, etc.
    ///
    /// This is needed because the Provider trait's fill method doesn't work
    /// well through generic trait bounds due to async trait limitations.
    async fn fill(&self, tx: N::TransactionRequest) -> TransportResult<SendableTx<N>>;

    /// Build and send a replacement transaction (cancel or gap fill).
    ///
    /// Creates a 0-value self-transfer with the specified nonce to replace
    /// a pending transaction or fill a nonce gap.
    async fn build_and_send_replacement_tx(
        &self,
        from: Address,
        nonce: u64,
        gas_source: TxGas,
        gas_multiplier: f64,
    ) -> TransportResult<(B256, SendableTx<N>, PendingTransactionBuilder<N>)>;
}

// ============================================================================
// NetworkProvider
// ============================================================================

/// A network provider that can optionally include wallet signing capability.
///
/// When created with `with_signer()`, also includes a `StatefulNonceManager`
/// for tracking nonce lifecycle.
///
/// ## Auto Recovery
///
/// By default, `auto_recovery` is enabled. This means:
/// - `send_transaction_ex()` will automatically retry on nonce errors
/// - `TrackedPendingTx::get_receipt()` will handle timeouts with recovery
///
/// To disable auto recovery:
/// ```ignore
/// let provider = provider.with_config(ProviderConfig::no_recovery());
/// ```
#[derive(Clone)]
pub enum NetworkProvider {
    /// HTTP provider without wallet signing
    Http {
        chain_id: u64,
        provider: FillProvider<BasicProvider, RootProvider>,
        receipt_timeout: Option<Duration>,
        nonce_manager: StatefulNonceManager,
        config: ProviderConfig,
    },
    /// Provider with wallet signing and nonce management
    Wallet {
        chain_id: u64,
        wallet: EthereumWallet,
        base: FillProvider<BasicProvider, RootProvider>,
        provider: FillProvider<JoinFill<BasicProvider, WalletFiller<EthereumWallet>>, RootProvider>,
        nonce_manager: StatefulNonceManager,
        receipt_timeout: Option<Duration>,
        config: ProviderConfig,
    },
}

impl ProviderEx<Ethereum> for NetworkProvider {
    fn chain_id(&self) -> u64 {
        match self {
            NetworkProvider::Http { chain_id, .. } => *chain_id,
            NetworkProvider::Wallet { chain_id, .. } => *chain_id,
        }
    }

    fn get_receipt_timeout(&self) -> Option<Duration> {
        match self {
            NetworkProvider::Http {
                receipt_timeout, ..
            } => receipt_timeout.clone(),
            NetworkProvider::Wallet {
                receipt_timeout, ..
            } => receipt_timeout.clone(),
        }
    }

    fn nonce_manager(&self) -> &StatefulNonceManager {
        match self {
            NetworkProvider::Http { nonce_manager, .. } => nonce_manager,
            NetworkProvider::Wallet { nonce_manager, .. } => nonce_manager,
        }
    }

    fn config(&self) -> &ProviderConfig {
        match self {
            NetworkProvider::Http { config, .. } => config,
            NetworkProvider::Wallet { config, .. } => config,
        }
    }

    /// Internal method to send a filled transaction.
    ///
    /// This is the core send method that all transaction sending goes through.
    /// Timeout should be applied by the caller using `with_timeout()`.
    async fn send_transaction_inner(
        &self,
        tx: SendableTx<Ethereum>,
    ) -> TransportResult<PendingTransactionBuilder<Ethereum>> {
        match self {
            NetworkProvider::Wallet { provider, .. } => {
                provider.send_transaction_internal(tx).await
            }
            NetworkProvider::Http { .. } => Err(RpcError::UnsupportedFeature(
                "Cannot send transaction without a signer",
            )),
        }
    }

    async fn fill(
        &self,
        tx: <Ethereum as Network>::TransactionRequest,
    ) -> TransportResult<SendableTx<Ethereum>> {
        match self {
            NetworkProvider::Wallet { provider, .. } => provider.fill(tx).await,
            NetworkProvider::Http { provider, .. } => provider.fill(tx).await,
        }
    }

    async fn send_transaction_ex(
        &self,
        tx: <Ethereum as Network>::TransactionRequest,
    ) -> TransportResult<TrackedPendingTx<Self, Ethereum>> {
        let config = self.config().clone();

        if !config.auto_recovery {
            // No recovery: direct send
            return self.try_send_transaction_ex(tx).await;
        }

        // With auto recovery: retry loop
        let from = match &tx.from {
            Some(addr) => *addr,
            None => self.from().map_err(|e| {
                RpcError::LocalUsageError(Box::new(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    e.to_string(),
                )))
            })?,
        };

        // Proactive recovery: check for abandoned nonces before sending
        // This prevents new transactions from getting stuck due to existing gaps
        let nonce_manager = self.nonce_manager();
        if let Some(status) = nonce_manager.get_status(from).await {
            if !status.abandoned_nonces.is_empty() {
                tracing::info!(
                    %from,
                    abandoned = ?status.abandoned_nonces,
                    "proactive recovery: filling abandoned nonces before send"
                );
                if let Err(e) = self.recover(from).await {
                    tracing::warn!(%from, error = %e, "proactive recovery failed, continuing anyway");
                }
            }
        }

        let mut retries = 0u32;

        loop {
            match self.try_send_transaction_ex(tx.clone()).await {
                Ok(tracked) => return Ok(tracked),

                Err(e) if retries >= config.max_send_retries => {
                    tracing::warn!(
                        %from, retries, error = %e,
                        "send_transaction_ex failed after max retries"
                    );
                    return Err(e);
                }

                Err(e) => {
                    let error_kind = classify_rpc_error(&e);
                    tracing::debug!(
                        %from, retries, error = %e, ?error_kind,
                        "send_transaction_ex failed, checking if recoverable"
                    );

                    match error_kind {
                        RpcErrorKind::NonceTooLow => {
                            // Local nonce is behind chain, sync and retry
                            tracing::info!(%from, "nonce too low, syncing from chain");
                            if let Err(sync_err) = self.nonce_manager().sync(self, from).await {
                                tracing::warn!(%from, error = %sync_err, "failed to sync nonce");
                                return Err(e);
                            }
                        }

                        RpcErrorKind::NonceTooHigh => {
                            // Gap exists, try to recover abandoned nonces
                            tracing::info!(%from, "nonce too high, recovering abandoned nonces");
                            if let Err(recover_err) = self.recover(from).await {
                                tracing::warn!(%from, error = %recover_err, "failed to recover nonces");
                                // Still retry - gap might resolve
                            }
                        }

                        RpcErrorKind::NetworkError => {
                            // Network error, wait and retry
                            let backoff = backoff_duration(retries, config.retry_backoff_ms);
                            tracing::debug!(%from, ?backoff, "network error, backing off");
                            tokio::time::sleep(backoff).await;
                        }

                        RpcErrorKind::AlreadyKnown => {
                            // Transaction already in mempool, this is actually okay
                            // But we don't have the TrackedPendingTx, so we need to fail
                            // User should check mempool or wait
                            tracing::info!(%from, "transaction already known in mempool");
                            return Err(e);
                        }

                        _ => {
                            // Non-recoverable error
                            if !error_kind.is_recoverable() {
                                tracing::debug!(%from, ?error_kind, "non-recoverable error");
                                return Err(e);
                            }
                            // Other recoverable errors: just retry with backoff
                            let backoff = backoff_duration(retries, config.retry_backoff_ms);
                            tokio::time::sleep(backoff).await;
                        }
                    }

                    retries += 1;
                }
            }
        }
    }

    async fn build_and_send_replacement_tx(
        &self,
        from: Address,
        nonce: u64,
        gas_source: TxGas,
        gas_multiplier: f64,
    ) -> TransportResult<(
        B256,
        SendableTx<Ethereum>,
        PendingTransactionBuilder<Ethereum>,
    )> {
        match self {
            NetworkProvider::Wallet { provider, .. } => {
                // Build replacement TX with gas pricing applied
                let tx = gas_source
                    .build_replacement_tx(from, nonce, provider, gas_multiplier)
                    .await?;

                tracing::debug!(
                    %from, nonce, gas_multiplier,
                    "built replacement transaction"
                );

                // Fill remaining fields (gas limit, chain_id) but NOT nonce (already set)
                let filled = provider.fill(tx).await?;

                // Send the replacement transaction
                let pending = self.send_transaction_inner(filled.clone()).await?;
                let tx_hash = *pending.tx_hash();

                Ok((tx_hash, filled, pending))
            }
            NetworkProvider::Http { .. } => Err(RpcError::UnsupportedFeature(
                "Cannot send transaction without a signer",
            )),
        }
    }
}

impl NetworkProvider {
    /// Create an HTTP provider without wallet signing
    pub async fn with_http(
        rpc_url: &str,
        polling_time: Option<Duration>,
        receipt_timeout: Option<Duration>,
        boost_gas_multiplier: u64,
    ) -> anyhow::Result<Self> {
        let nonce_manager = StatefulNonceManager::new();
        let http_provider = ProviderBuilder::new()
            .disable_recommended_fillers()
            .filler(ChainIdFiller::default())
            .filler(BoostGasFiller::multiplied(boost_gas_multiplier))
            .filler(BlobGasFiller::default())
            .filler(NonceFiller::new(nonce_manager.clone()))
            .connect_http(rpc_url.parse()?);
        if let Some(polling_time) = polling_time {
            http_provider.client().set_poll_interval(polling_time);
        }
        let chain_id = http_provider.get_chain_id().await?;

        Ok(Self::Http {
            chain_id,
            provider: http_provider,
            receipt_timeout,
            nonce_manager,
            config: ProviderConfig::default(),
        })
    }

    /// Create a provider with wallet capability for signing transactions.
    ///
    /// Also creates a new `StatefulNonceManager` for tracking nonce lifecycle.
    pub fn with_signer(&self, signer: PrivateKeySigner) -> Self {
        let wallet = EthereumWallet::new(signer);
        match self {
            NetworkProvider::Http {
                chain_id,
                provider,
                nonce_manager,
                receipt_timeout,
                config,
            } => {
                // Build a new provider with our StatefulNonceManager
                let base = provider.clone();
                let provider = base.clone().join_with(WalletFiller::new(wallet.clone()));
                NetworkProvider::Wallet {
                    chain_id: *chain_id,
                    wallet,
                    base,
                    provider,
                    receipt_timeout: receipt_timeout.clone(),
                    nonce_manager: nonce_manager.clone(),
                    config: config.clone(),
                }
            }
            NetworkProvider::Wallet {
                chain_id,
                base,
                nonce_manager,
                receipt_timeout,
                config,
                ..
            } => {
                let provider = base.clone().join_with(WalletFiller::new(wallet.clone()));
                NetworkProvider::Wallet {
                    chain_id: *chain_id,
                    wallet,
                    base: base.clone(),
                    provider,
                    nonce_manager: nonce_manager.clone(),
                    receipt_timeout: *receipt_timeout,
                    config: config.clone(),
                }
            }
        }
    }

    /// Update the provider configuration.
    ///
    /// ## Example
    ///
    /// ```ignore
    /// // Disable auto recovery
    /// let provider = provider.with_config(ProviderConfig::no_recovery());
    ///
    /// // Custom config
    /// let provider = provider.with_config(ProviderConfig::default()
    ///     .with_auto_recovery(true)
    ///     .with_gas_multiplier(1.2)
    ///     .with_max_retries(5));
    /// ```
    pub fn with_config(mut self, new_config: ProviderConfig) -> Self {
        match &mut self {
            NetworkProvider::Http { config, .. } => {
                *config = new_config;
            }
            NetworkProvider::Wallet { config, .. } => *config = new_config,
        }
        self
    }

    pub fn with_rebroadcast(mut self, rebroadcast: RebroadcastConfig) -> Self {
        let cfg = match &mut self {
            NetworkProvider::Http { config, .. } => config,
            NetworkProvider::Wallet { config, .. } => config,
        };
        cfg.rebroadcast = rebroadcast;
        self
    }

    pub fn with_rebroadcast_interval(mut self, interval: Duration) -> Self {
        let cfg = match &mut self {
            NetworkProvider::Http { config, .. } => config,
            NetworkProvider::Wallet { config, .. } => config,
        };
        cfg.rebroadcast.interval = interval;
        self
    }

    /// Update the receipt timeout.
    ///
    /// This is useful for testing timeout scenarios.
    pub fn with_receipt_timeout(mut self, timeout: Duration) -> Self {
        match &mut self {
            NetworkProvider::Http {
                receipt_timeout, ..
            } => {
                receipt_timeout.replace(timeout);
            }
            NetworkProvider::Wallet {
                receipt_timeout, ..
            } => {
                receipt_timeout.replace(timeout);
            }
        }
        self
    }

    /// Get the signer address if this provider has a wallet
    pub fn from(&self) -> anyhow::Result<Address> {
        match self {
            NetworkProvider::Http { .. } => anyhow::bail!("Provider has no signer"),
            NetworkProvider::Wallet { wallet, .. } => {
                Ok(<EthereumWallet as NetworkWallet<Ethereum>>::default_signer_address(wallet))
            }
        }
    }

    /// Fill a nonce gap by sending a cancel transaction.
    ///
    /// When a transaction is abandoned (dropped without confirmation), it may create
    /// a gap that blocks subsequent transactions. This method fills the gap by sending
    /// a "cancel" transaction: 0 ETH to self with the specified nonce.
    ///
    /// ## Parameters
    ///
    /// - `nonce`: The nonce to fill (should be from `get_abandoned_nonces()`)
    /// - `original_tx_hash`: The hash of the original abandoned transaction
    /// - `gas_price_multiplier`: Multiplier for gas price (e.g., 1.1 = 10% higher).
    ///   If the original tx is still in mempool, we need higher gas to replace it.
    ///
    /// ## Returns
    ///
    /// Returns the pending transaction for the cancel transaction. The caller should
    /// wait for confirmation and then call `nonce_manager.confirm()` to clear the slot.
    ///
    /// ## Note
    ///
    /// Before calling this method, you should check if the original transaction was
    /// actually mined using `provider.get_transaction_receipt(original_tx_hash)`.
    /// If it was mined, call `nonce_manager.confirm(nonce)` instead.
    pub async fn fill_nonce_gap(
        &self,
        nonce: u64,
        _original_tx_hash: B256,
        gas_price_multiplier: f64,
    ) -> TransportResult<TrackedPendingTx<Self, Ethereum>> {
        match self {
            NetworkProvider::Wallet {
                nonce_manager,
                receipt_timeout,
                ..
            } => {
                let from = self.from().map_err(|e| {
                    RpcError::LocalUsageError(Box::new(std::io::Error::new(
                        std::io::ErrorKind::Other,
                        e.to_string(),
                    )))
                })?;

                // Use shared helper with network gas estimation
                let (tx_hash, filled, pending) = match self
                    .build_and_send_replacement_tx(
                        from,
                        nonce,
                        TxGas::FromNetwork,
                        gas_price_multiplier,
                    )
                    .await
                {
                    Ok(result) => result,
                    Err(e) => {
                        tracing::warn!(
                            %from, nonce, error = %e,
                            "failed to send cancel transaction for gap filling"
                        );
                        return Err(e);
                    }
                };

                let pending = pending.with_timeout(*receipt_timeout);

                // Mark as sent (transition from Abandoned to Pending)
                nonce_manager.mark_sent(from, nonce, tx_hash).await;
                tracing::info!(
                    %from, nonce, %tx_hash,
                    "sent cancel transaction to fill nonce gap"
                );

                // Get atomic state from the existing slot (should exist since it's abandoned)
                let atomic_state = nonce_manager
                    .get_slot_atomic_state(from, nonce)
                    .await
                    .unwrap_or_else(|| {
                        // Fallback: create a new atomic state in PENDING state
                        let state = Arc::new(AtomicNonceState::new_reserved());
                        state.mark_pending();
                        state
                    });

                Ok(TrackedPendingTx::new(
                    self.clone(),
                    pending,
                    from,
                    nonce,
                    atomic_state,
                    filled,
                ))
            }
            NetworkProvider::Http { .. } => Err(RpcError::UnsupportedFeature(
                "Cannot send transaction without a signer",
            )),
        }
    }

    /// Internal method: try to send transaction once without retry logic.
    ///
    /// This is the core implementation used by `send_transaction_ex`.
    async fn try_send_transaction_ex(
        &self,
        tx: <Ethereum as Network>::TransactionRequest,
    ) -> TransportResult<TrackedPendingTx<Self, Ethereum>> {
        match self {
            NetworkProvider::Wallet {
                provider,
                nonce_manager,
                receipt_timeout,
                wallet,
                ..
            } => {
                let from = match tx.from {
                    Some(addr) => addr,
                    None => wallet.default_signer().address(),
                };

                // Get the next nonce that will be allocated (for cleanup on fill failure)
                // If no status exists yet, the first nonce will be 0
                let expected_nonce = nonce_manager
                    .get_status(from)
                    .await
                    .map(|s| s.next_nonce)
                    .unwrap_or(0);

                // Fill the transaction (this allocates nonce via NonceFiller)
                let filled = match provider.fill(tx).await {
                    Ok(filled) => filled,
                    Err(mut e) => {
                        e = pretty_rpc_error(e);
                        // fill() failed (e.g., gas estimation error)
                        // Check if nonce was allocated by comparing with current state
                        if let Some(status) = nonce_manager.get_status(from).await {
                            if status.next_nonce > expected_nonce {
                                // Nonce was allocated during fill, release it
                                // The allocated nonce is next_nonce - 1 (the one just taken)
                                let allocated_nonce = status.next_nonce - 1;
                                nonce_manager.release(from, allocated_nonce).await;
                                tracing::warn!(
                                    %from, nonce = allocated_nonce, error = %e,
                                    "released nonce after fill failure (gas estimation)"
                                );
                            }
                        }
                        return Err(e);
                    }
                };

                // Extract nonce and raw_tx from the filled (signed) transaction
                let envelope = filled
                    .as_envelope()
                    .expect("should be an envelope after fill with WalletFiller");
                let nonce = envelope.nonce();

                // Get atomic_state from the slot (created during fill)
                let atomic_state = nonce_manager
                    .get_slot_atomic_state(from, nonce)
                    .await
                    .expect("slot should exist after fill");

                // Send the transaction (with nonce rollback on failure)
                let pending = match self.send_transaction_inner(filled.clone()).await {
                    Ok(pending) => pending,
                    Err(e) => {
                        // Release the nonce on send failure
                        nonce_manager.release(from, nonce).await;
                        tracing::warn!(%from, nonce, error = %e, "released nonce after send failure");
                        return Err(e);
                    }
                };
                let pending = pending.with_timeout(*receipt_timeout);

                // Mark nonce as sent (transition from Reserved to Pending)
                let tx_hash = *pending.tx_hash();
                nonce_manager.mark_sent(from, nonce, tx_hash).await;
                tracing::debug!(%from, nonce, %tx_hash, "marked nonce as sent");

                Ok(TrackedPendingTx::new(
                    self.clone(),
                    pending,
                    from,
                    nonce,
                    atomic_state,
                    filled,
                ))
            }
            NetworkProvider::Http { .. } => Err(RpcError::UnsupportedFeature(
                "Cannot send transaction without a signer",
            )),
        }
    }

    /// Recover all abandoned nonces for an address.
    ///
    /// This method:
    /// 1. Gets all abandoned nonces for the address
    /// 2. For each abandoned nonce (in order):
    ///    - Checks if the original transaction was actually mined
    ///    - If mined: confirms the nonce
    ///    - If not mined: sends a cancel transaction to fill the gap
    ///
    /// ## Example
    ///
    /// ```ignore
    /// // Manual recovery
    /// let result = provider.recover(address).await?;
    /// println!("Recovered {} nonces", result.recovered_count);
    /// ```
    pub async fn recover(&self, address: Address) -> anyhow::Result<RecoveryResult> {
        self.recover_with_options(address, RecoveryOptions::default())
            .await
    }

    /// Recover abandoned nonces with custom options.
    pub async fn recover_with_options(
        &self,
        address: Address,
        options: RecoveryOptions,
    ) -> anyhow::Result<RecoveryResult> {
        let nonce_manager = self.nonce_manager();
        let abandoned = nonce_manager.get_abandoned_nonces(address).await;

        let mut result = RecoveryResult::new(address);

        if abandoned.is_empty() {
            tracing::debug!(%address, "no abandoned nonces to recover");
            return Ok(result);
        }

        tracing::info!(
            %address,
            count = abandoned.len(),
            "starting recovery for abandoned nonces"
        );

        // Process abandoned nonces in order (important for sequential nonces)
        for (nonce, original_tx_hash) in abandoned.into_iter().take(options.max_nonces) {
            // 1. Check if original transaction was actually mined
            match self.get_transaction_receipt(original_tx_hash).await {
                Ok(Some(_receipt)) => {
                    // Transaction was mined, just confirm the nonce
                    nonce_manager.confirm(address, nonce).await;
                    tracing::info!(
                        %address, nonce, %original_tx_hash,
                        "abandoned nonce was actually mined, confirmed"
                    );
                    result.add_result(SingleRecoveryResult::AlreadyMined {
                        nonce,
                        original_tx_hash,
                    });
                    continue;
                }
                Ok(None) => {
                    // Transaction not mined, need to fill gap
                    tracing::debug!(
                        %address, nonce, %original_tx_hash,
                        "abandoned nonce not mined, filling gap"
                    );
                }
                Err(e) => {
                    // Error checking receipt, try to fill gap anyway
                    tracing::warn!(
                        %address, nonce, %original_tx_hash, error = %e,
                        "error checking receipt, attempting gap fill"
                    );
                }
            }

            // 2. Send cancel transaction to fill the gap
            match self
                .fill_nonce_gap(nonce, original_tx_hash, options.gas_multiplier)
                .await
            {
                Ok(mut cancel_tx) => {
                    let cancel_tx_hash = cancel_tx.tx_hash();

                    // Wait for cancel tx to be mined
                    match cancel_tx.get_receipt().await {
                        Ok(_) => {
                            tracing::info!(
                                %address, nonce, %cancel_tx_hash,
                                "gap filled successfully"
                            );
                            result.add_result(SingleRecoveryResult::GapFilled {
                                nonce,
                                original_tx_hash,
                                cancel_tx_hash,
                            });
                        }
                        Err(e) => {
                            tracing::warn!(
                                %address, nonce, %cancel_tx_hash, error = %e,
                                "cancel tx failed to confirm"
                            );
                            result.add_result(SingleRecoveryResult::Failed {
                                nonce,
                                original_tx_hash,
                                error: e.to_string(),
                            });

                            if !options.continue_on_failure {
                                return Ok(result);
                            }
                        }
                    }
                }
                Err(e) => {
                    tracing::warn!(
                        %address, nonce, %original_tx_hash, error = %e,
                        "failed to send cancel tx for gap filling"
                    );
                    result.add_result(SingleRecoveryResult::Failed {
                        nonce,
                        original_tx_hash,
                        error: e.to_string(),
                    });

                    if !options.continue_on_failure {
                        return Ok(result);
                    }
                }
            }
        }

        tracing::info!(
            %address,
            recovered = result.recovered_count,
            failed = result.failed_count,
            "recovery completed"
        );

        Ok(result)
    }
}

// ============================================================================
// Provider trait implementation
// ============================================================================

#[async_trait::async_trait]
impl Provider<Ethereum> for NetworkProvider {
    fn root(&self) -> &alloy::providers::RootProvider<Ethereum> {
        match self {
            NetworkProvider::Http { provider, .. } => provider.root(),
            NetworkProvider::Wallet { provider, .. } => provider.root(),
        }
    }

    /// Send a transaction.
    ///
    /// For `Wallet` variant, this uses the wallet to sign and the nonce filler
    /// (with StatefulNonceManager) to assign nonces.
    async fn send_transaction(
        &self,
        tx: <Ethereum as Network>::TransactionRequest,
    ) -> TransportResult<PendingTransactionBuilder<Ethereum>> {
        match self {
            NetworkProvider::Http { .. } => TransportResult::Err(RpcError::UnsupportedFeature(
                "Cannot send transaction without a signer",
            )),
            NetworkProvider::Wallet {
                provider,
                receipt_timeout,
                ..
            } => {
                let n = provider.fill(tx).await?;
                let pending_tx = self.send_transaction_inner(n).await?;
                Ok(pending_tx.with_timeout(*receipt_timeout))
            }
        }
    }
}
