//! Transaction builder with nonce lifecycle tracking.
//!
//! This module provides `TrackedPendingTx` and `CallBuilderEx` trait for sending
//! transactions with automatic nonce lifecycle management.
//!
//! ## Key Components
//!
//! - **TrackedPendingTx**: Wraps `PendingTransactionBuilder` with nonce tracking.
//!   Automatically confirms nonce on receipt success, marks as abandoned on drop.
//!
//! - **TxResolution**: Enum representing resolved transaction state (Confirmed/Cancelled/Timeout).
//!
//! - **CallBuilderEx**: Extension trait for alloy's `CallBuilder` to use `send_ex()`.
//!
//! ## Automatic Nonce Management
//!
//! ```text
//! send_transaction_ex() → TrackedPendingTx (nonce: PENDING)
//!                              │
//!         ┌────────────────────┴────────────────────┐
//!         │                                         │
//!   get_receipt() success                     Drop without receipt
//!         │                                         │
//!         ▼                                         ▼
//!   nonce: CONFIRMED                         nonce: ABANDONED
//! ```
//!
//! ## Rebroadcasting
//!
//! `TrackedPendingTx::get_receipt()` optionally rebroadcasts the transaction
//! at configurable intervals to prevent mempool eviction. This is especially
//! useful for slow-confirming transactions on congested networks.

use std::{future::IntoFuture, sync::Arc, time::Duration};

use alloy::{
    contract::{CallBuilder, CallDecoder, EthCall, Result as ContractResult},
    network::Network,
    primitives::{Address, B256},
    providers::{PendingTransactionBuilder, SendableTx},
};
use tokio::time::{interval, MissedTickBehavior};

use crate::ext::{
    pretty_error, AtomicNonceState, ProviderEx, StatefulNonceManager, TxGas, TxResolution,
};

use super::error::{classify_rpc_error, is_timeout_error, RpcErrorKind};

// ============================================================================
// Tx State
// ============================================================================

/// Tx state for TrackedPendingTx
enum TxState<N: Network> {
    /// Transaction submitted but not yet confirmed
    Pending(PendingTransactionBuilder<N>),
    /// Transaction resolved
    Resolved(TxResolution<N>),
}

impl<N: Network> TxState<N> {
    pub fn resolved(&mut self, res: TxResolution<N>) -> &TxResolution<N> {
        *self = TxState::Resolved(res);
        match self {
            TxState::Resolved(r) => r,
            _ => unreachable!(),
        }
    }
}

// ============================================================================
// TrackedPendingTx - wraps pending tx with nonce tracking info
// ============================================================================

/// A pending transaction with tracked nonce information and automatic nonce lifecycle management.
///
/// ## Nonce Lifecycle
///
/// `TrackedPendingTx` automatically manages the nonce state:
///
/// - **On `get_receipt()` success**: The nonce is marked as CONFIRMED and the slot is cleaned up.
/// - **On `Drop` without confirmation**: The nonce is marked as ABANDONED (may need gap filling).
///
/// ## Rebroadcasting
///
/// When `rebroadcast` is enabled in `ProviderConfig`, `get_receipt()` will periodically
/// rebroadcast the signed transaction to ensure it stays in the mempool and gets propagated
/// to miners/validators. This helps prevent transactions from being dropped due to:
/// - Mempool eviction (low gas price)
/// - Network partitions
/// - Node restarts
///
/// ## Example
///
/// ```ignore
/// // Normal usage - nonce confirmed automatically
/// let tracked = provider.send_transaction_ex(tx).await?;
/// let receipt = tracked.get_receipt().await?;  // nonce confirmed here
///
/// // Fire-and-forget - nonce marked abandoned on drop
/// let tracked = provider.send_transaction_ex(tx).await?;
/// drop(tracked);  // nonce marked as ABANDONED
/// ```
pub struct TrackedPendingTx<P: ProviderEx<N>, N: Network> {
    pub(crate) provider: P,
    /// The underlying transaction state (pending or resolved)
    state: TxState<N>,
    /// The address that sent the transaction
    address: Address,
    /// The nonce used for this transaction
    nonce: u64,
    /// Atomic state handle for lock-free state transitions
    atomic_state: Arc<AtomicNonceState>,
    /// Raw signed transaction bytes for rebroadcasting
    pub(crate) raw_tx: SendableTx<N>,
    /// Original transaction hash (stable across all states)
    original_tx_hash: B256,
}

impl<P: ProviderEx<N>, N: Network> TrackedPendingTx<P, N>
where
    N::TxEnvelope: Clone,
{
    /// Create a new TrackedPendingTx
    pub(crate) fn new(
        provider: P,
        inner: PendingTransactionBuilder<N>,
        address: Address,
        nonce: u64,
        atomic_state: Arc<AtomicNonceState>,
        filled: SendableTx<N>,
    ) -> Self {
        let original_tx_hash = *inner.tx_hash();
        Self {
            provider,
            state: TxState::Pending(inner),
            address,
            nonce,
            atomic_state,
            raw_tx: filled,
            original_tx_hash,
        }
    }

    /// Get the ORIGINAL transaction hash (not cancel TX hash).
    ///
    /// This is stable across all resolution states, even if the transaction
    /// was cancelled and a different TX was mined.
    pub fn tx_hash(&self) -> B256 {
        self.original_tx_hash
    }

    /// Get the address that sent the transaction
    pub fn address(&self) -> Address {
        self.address
    }

    /// Get the nonce used for this transaction
    pub fn nonce(&self) -> u64 {
        self.nonce
    }

    /// Get the nonce manager
    pub fn nonce_manager(&self) -> &StatefulNonceManager {
        self.provider.nonce_manager()
    }

    /// Get the atomic state handle for lock-free state checks/transitions
    pub fn atomic_state(&self) -> &Arc<AtomicNonceState> {
        &self.atomic_state
    }

    /// Phase 1: Wait for transaction confirmation with rebroadcasting.
    ///
    /// On timeout, checks chain state to verify if TX was actually mined.
    /// Returns the resolved state on success, timeout error if not mined.
    async fn wait_for_confirmation(&mut self) -> anyhow::Result<&TxResolution<N>> {
        // Check if already resolved (use matches! to avoid holding reference)
        // Extract pending state components
        let (provider_root, pending_config) = match self.state {
            TxState::Pending(ref pending) => (pending.provider().clone(), pending.inner().clone()),
            TxState::Resolved(ref res) => return Ok(res),
        };

        let config = self.provider.config().clone();

        // Create interval for rebroadcasting
        let mut rebroadcast_ticker = interval(config.rebroadcast.interval);
        rebroadcast_ticker.set_missed_tick_behavior(MissedTickBehavior::Skip);
        rebroadcast_ticker.tick().await; // Skip first immediate tick

        // Build the receipt future using cloned components
        let receipt_fut = async {
            PendingTransactionBuilder::from_config(provider_root, pending_config)
                .get_receipt()
                .await
        };
        tokio::pin!(receipt_fut);

        loop {
            tokio::select! {
                result = &mut receipt_fut => {
                    match result {
                        Ok(receipt) => {
                            self.confirm_nonce().await;
                            return Ok(self.state.resolved(TxResolution::Confirmed { receipt }));
                        }
                        Err(e) => {
                            let error: anyhow::Error = e.into();

                            // On timeout, check chain state to confirm TX status
                            if is_timeout_error(&error) {
                                tracing::debug!(
                                    address = %self.address,
                                    nonce = self.nonce,
                                    tx_hash = %self.tx_hash(),
                                    "receipt timeout, checking chain state"
                                );

                                if let Some(receipt) = self.check_chain_state().await? {
                                    return Ok(self.state.resolved(TxResolution::Confirmed { receipt }));
                                }
                            }

                            return Err(error);
                        }
                    }
                }

                _ = rebroadcast_ticker.tick(), if config.rebroadcast.enabled => {
                    self.rebroadcast_tx(&self.raw_tx, self.tx_hash()).await;
                }
            }
        }
    }

    /// Helper to get the resolved state, panics if still pending.
    fn expect_resolved(&self) -> anyhow::Result<&TxResolution<N>> {
        match &self.state {
            TxState::Resolved(res) => Ok(res),
            TxState::Pending { .. } => unreachable!("expected resolved state"),
        }
    }

    /// Rebroadcast any transaction to the network
    async fn rebroadcast_tx(&self, raw_tx: &SendableTx<N>, tx_hash: B256) {
        match self.provider.send_transaction_inner(raw_tx.clone()).await {
            Ok(_) => {
                tracing::debug!(
                    address = %self.address,
                    nonce = self.nonce,
                    %tx_hash,
                    "rebroadcast successful"
                );
            }
            Err(e) => {
                let kind = classify_rpc_error(&e);
                match kind {
                    RpcErrorKind::AlreadyKnown => {
                        tracing::trace!(
                            address = %self.address,
                            nonce = self.nonce,
                            %tx_hash,
                            "rebroadcast: tx still in mempool"
                        );
                    }
                    RpcErrorKind::NonceTooLow => {
                        tracing::debug!(
                            address = %self.address,
                            nonce = self.nonce,
                            %tx_hash,
                            "rebroadcast: nonce used, tx may be mined"
                        );
                    }
                    _ => {
                        tracing::warn!(
                            address = %self.address,
                            nonce = self.nonce,
                            %tx_hash,
                            error = %e,
                            "rebroadcast failed"
                        );
                    }
                }
            }
        }
    }

    /// Internal: confirm the nonce after successful receipt
    async fn confirm_nonce(&self) {
        // Mark nonce as confirmed (lock-free atomic operation)
        self.atomic_state.mark_confirmed();

        // Also confirm via nonce_manager to clean up the slot
        self.nonce_manager().confirm(self.address, self.nonce).await;

        tracing::debug!(
            address = %self.address,
            nonce = self.nonce,
            tx_hash = %self.tx_hash(),
            "nonce confirmed after receipt"
        );
    }

    /// Check on-chain state to verify if the transaction was mined.
    ///
    /// Returns Some(receipt) if the transaction was actually mined, None otherwise.
    async fn check_chain_state(&mut self) -> anyhow::Result<Option<N::ReceiptResponse>> {
        let tx_hash = self.tx_hash();

        // Check if transaction is actually on chain
        match self.provider.get_transaction_receipt(tx_hash).await {
            Ok(Some(receipt)) => {
                // Transaction was mined! Confirm the nonce.
                tracing::info!(
                    address = %self.address,
                    nonce = self.nonce,
                    %tx_hash,
                    "transaction was actually mined despite timeout"
                );
                self.confirm_nonce().await;
                Ok(Some(receipt))
            }
            Ok(None) => {
                // Transaction not mined, mark as abandoned
                tracing::debug!(
                    address = %self.address,
                    nonce = self.nonce,
                    %tx_hash,
                    "transaction not found on chain, marking as abandoned"
                );
                self.atomic_state.mark_abandoned();
                Ok(None)
            }
            Err(e) => {
                // Error checking chain, be conservative and mark as abandoned
                tracing::warn!(
                    address = %self.address,
                    nonce = self.nonce,
                    %tx_hash,
                    error = %e,
                    "error checking chain state, marking as abandoned"
                );
                self.atomic_state.mark_abandoned();
                Err(e.into())
            }
        }
    }

    /// Phase 2: Race original vs cancel TX for confirmation.
    ///
    /// Uses Alloy's `PendingTransactionBuilder::get_receipt()` for both transactions
    /// and races them with `select!`. First confirmation wins. Rebroadcasts only
    /// the cancel TX. Returns the resolution after updating `self.state`.
    async fn race_for_confirmation(
        &mut self,
        original_tx_hash: B256,
        cancel_tx_hash: B256,
        cancel_raw_tx: SendableTx<N>,
        timeout: Duration,
    ) -> anyhow::Result<&TxResolution<N>> {
        // Extract root provider from pending state
        let provider_root = match self.state {
            TxState::Pending(ref pending) => pending.provider().clone(),
            TxState::Resolved(ref res) => return Ok(res),
        };

        let config = self.provider.config();

        // Create pending transaction builders for both TXs with same timeout
        let original_pending =
            PendingTransactionBuilder::new(provider_root.clone(), original_tx_hash)
                .with_timeout(Some(timeout));
        let cancel_pending = PendingTransactionBuilder::new(provider_root, cancel_tx_hash)
            .with_timeout(Some(timeout));

        // Create receipt futures
        let original_fut = original_pending.get_receipt();
        let cancel_fut = cancel_pending.get_receipt();
        tokio::pin!(original_fut);
        tokio::pin!(cancel_fut);

        // Track which futures have completed (with error/timeout)
        let mut original_done = false;
        let mut cancel_done = false;

        // Rebroadcast ticker for cancel TX only
        let mut rebroadcast_ticker = interval(config.rebroadcast.interval);
        rebroadcast_ticker.set_missed_tick_behavior(MissedTickBehavior::Skip);
        rebroadcast_ticker.tick().await; // Skip first immediate tick

        loop {
            // Check if both futures have finished (both timed out/errored)
            if original_done && cancel_done {
                tracing::warn!(
                    address = %self.address,
                    nonce = self.nonce,
                    original = %original_tx_hash,
                    cancel = %cancel_tx_hash,
                    "Phase 2 timeout - both TXs unconfirmed, marking as ABANDONED"
                );
                self.atomic_state.mark_abandoned();
                return Ok(self.state.resolved(TxResolution::Timeout {
                    original_tx_hash,
                    cancel_tx_hash,
                    nonce: self.nonce,
                }));
            }

            tokio::select! {
                // Race original TX receipt
                result = &mut original_fut, if !original_done => {
                    match result {
                        Ok(receipt) => {
                            tracing::info!(
                                address = %self.address,
                                nonce = self.nonce,
                                %original_tx_hash,
                                "Original TX confirmed in Phase 2"
                            );

                            self.confirm_nonce().await;
                            return Ok(self.state.resolved(TxResolution::OriginalConfirmedAfterCancel {
                                receipt,
                                cancel_tx_hash,
                            }));
                        }
                        Err(e) => {
                            // Timeout or error - mark as done, maybe cancel will win
                            tracing::debug!(
                                address = %self.address,
                                nonce = self.nonce,
                                %original_tx_hash,
                                error = %e,
                                "Original TX receipt future completed with error"
                            );
                            original_done = true;
                        }
                    }
                }

                // Race cancel TX receipt
                result = &mut cancel_fut, if !cancel_done => {
                    match result {
                        Ok(cancel_receipt) => {
                            tracing::info!(
                                address = %self.address,
                                nonce = self.nonce,
                                %cancel_tx_hash,
                                "Cancel TX confirmed in Phase 2"
                            );
                            self.confirm_nonce().await;
                            return Ok(self.state.resolved(TxResolution::Cancelled {
                                cancel_receipt,
                                original_tx_hash,
                            }));
                        }
                        Err(e) => {
                            // Timeout or error - mark as done, maybe original will win
                            tracing::debug!(
                                address = %self.address,
                                nonce = self.nonce,
                                %cancel_tx_hash,
                                error = %e,
                                "Cancel TX receipt future completed with error"
                            );
                            cancel_done = true;
                        }
                    }
                }

                // Rebroadcast cancel TX only (while it's still pending)
                _ = rebroadcast_ticker.tick(), if config.rebroadcast.enabled && !cancel_done => {
                    self.rebroadcast_tx(&cancel_raw_tx, cancel_tx_hash).await;
                }
            }
        }
    }

    /// Build and send a cancel transaction (0 ETH to self with same nonce).
    ///
    /// Uses the same gas pricing type as the original transaction (EIP-1559 or legacy)
    /// with the gas prices multiplied by `gas_multiplier`.
    async fn send_cancel_tx(&self, gas_multiplier: f64) -> anyhow::Result<(B256, SendableTx<N>)> {
        // Get gas config from the original transaction
        let original_envelope = self
            .raw_tx
            .as_envelope()
            .expect("raw_tx should be an envelope");

        // Use shared helper with gas from original envelope
        let (tx_hash, filled, _pending) = self
            .provider
            .build_and_send_replacement_tx(
                self.address,
                self.nonce,
                TxGas::from_envelope::<N>(original_envelope),
                gas_multiplier,
            )
            .await?;

        // Note: We don't call mark_sent again since we're using the same nonce
        // that's already marked as PENDING

        Ok((tx_hash, filled))
    }

    /// Get the transaction receipt using default cancel behavior from config.
    ///
    /// Convenience method that calls [`resolution()`](Self::resolution) and extracts the receipt.
    /// Only succeeds if the original transaction was confirmed (not cancelled or timed out).
    ///
    /// For full control over all resolution outcomes, use [`resolution()`](Self::resolution) instead.
    pub async fn get_receipt(&mut self) -> anyhow::Result<&N::ReceiptResponse> {
        self.resolution().await?.receipt()
    }

    /// Get the full transaction resolution using default cancel behavior from config.
    ///
    /// Uses `CancelConfig::enabled` from provider config to determine whether to send
    /// a cancel transaction on timeout. For explicit control, use [`resolution_ex()`](Self::resolution_ex).
    pub async fn resolution(&mut self) -> anyhow::Result<&TxResolution<N>> {
        self.resolution_ex(self.provider.config().cancel.enabled)
            .await
    }

    /// Get the full transaction resolution with explicit cancel behavior.
    ///
    /// ## Parameters
    ///
    /// - `cancel_on_timeout`: Controls cancel behavior on timeout:
    ///   - `Some(true)`: Send cancel TX on timeout and race both transactions
    ///   - `Some(false)`: Return error on timeout without cancel attempt
    ///   - `None`: Use `CancelConfig::enabled` from provider config (default)
    ///
    /// ## Flow (when `cancel_on_timeout = true`)
    ///
    /// 1. **Phase 1**: Wait for receipt with rebroadcasting
    /// 2. **On Phase 1 timeout**: Send cancel TX with 2x gas price, same nonce
    /// 3. **Phase 2**: Race original vs cancel TX for confirmation
    /// 4. **Return**: `&TxResolution` reference indicating which TX was mined (or both timed out)
    ///
    /// ## Flow (when `cancel_on_timeout = false`)
    ///
    /// 1. Wait for receipt with rebroadcasting
    /// 2. On timeout: check chain state, return error if not mined
    ///
    /// ## Configuration
    ///
    /// Cancel behavior is configured via `CancelConfig` in `ProviderConfig`:
    /// - `gas_multiplier`: Gas price multiplier for cancel TX (default: 2.0)
    /// - `phase2_timeout_multiplier`: Phase 2 timeout = receipt_timeout * multiplier (default: 5.0)
    /// - `phase2_timeout`: Optional explicit Phase 2 timeout
    ///
    /// ## Example
    ///
    /// ```ignore
    /// let mut tracked = provider.send_transaction_ex(tx).await?;
    /// // Use default behavior from config
    /// let resolution = tracked.resolution().await?;
    /// // Or explicitly enable cancel on timeout
    /// let resolution = tracked.resolution_ex(true).await?;
    /// match resolution {
    ///     TxResolution::Confirmed { receipt } => {
    ///         println!("TX confirmed: {}", receipt.transaction_hash);
    ///     }
    ///     TxResolution::OriginalConfirmedAfterCancel { receipt, cancel_tx_hash } => {
    ///         println!("Original TX confirmed after cancel attempt");
    ///     }
    ///     TxResolution::Cancelled { cancel_receipt, original_tx_hash } => {
    ///         println!("TX cancelled, original {} replaced", original_tx_hash);
    ///     }
    ///     TxResolution::Timeout { original_tx_hash, cancel_tx_hash, nonce } => {
    ///         eprintln!("Both TXs timed out - manual check required");
    ///     }
    /// }
    /// ```
    pub async fn resolution_ex(
        &mut self,
        cancel_on_timeout: bool,
    ) -> anyhow::Result<&TxResolution<N>> {
        // Phase 1: Wait for confirmation (checks chain state on timeout)
        match self.wait_for_confirmation().await {
            Ok(_) => return self.expect_resolved(),
            Err(e) if is_timeout_error(&e) && cancel_on_timeout => {
                // Continue to Phase 2
                tracing::info!(
                    address = %self.address,
                    nonce = self.nonce,
                    tx_hash = %self.tx_hash(),
                    "Phase 1 timeout, sending cancel transaction"
                );
            }
            Err(e) => return Err(e),
        }

        let original_tx_hash = self.tx_hash();
        let config = self.provider.config().clone();

        // Send cancel transaction
        let (cancel_tx_hash, cancel_raw_tx) =
            self.send_cancel_tx(config.cancel.gas_multiplier).await?;

        tracing::info!(
            address = %self.address,
            nonce = self.nonce,
            original = %original_tx_hash,
            cancel = %cancel_tx_hash,
            "Cancel TX sent, entering Phase 2"
        );

        // Calculate Phase 2 timeout
        let receipt_timeout = self
            .provider
            .get_receipt_timeout()
            .unwrap_or(Duration::from_secs(120));
        let phase2_timeout = config.cancel.phase2_timeout.unwrap_or_else(|| {
            Duration::from_secs_f64(
                receipt_timeout.as_secs_f64() * config.cancel.phase2_timeout_multiplier,
            )
        });

        // Phase 2: Race original vs cancel
        self.race_for_confirmation(
            original_tx_hash,
            cancel_tx_hash,
            cancel_raw_tx,
            phase2_timeout,
        )
        .await
    }
}

// ============================================================================
// Drop implementation - mark nonce as abandoned if still pending
// ============================================================================

impl<P: ProviderEx<N>, N: Network> Drop for TrackedPendingTx<P, N> {
    fn drop(&mut self) {
        // Mark the nonce as abandoned using lock-free atomic operation
        if self.atomic_state.mark_abandoned() {
            tracing::debug!(
                address = %self.address,
                nonce = self.nonce,
                "nonce marked as ABANDONED on TrackedPendingTx drop"
            );
        }
    }
}

// ============================================================================
// CallBuilderEx trait
// ============================================================================

#[allow(async_fn_in_trait)]
pub trait CallBuilderEx<P: ProviderEx<N>, D: CallDecoder, N: Network> {
    /// Send transaction with nonce tracking.
    ///
    /// Returns a `TrackedPendingTx` that contains the assigned nonce,
    /// which can be used to confirm the nonce after transaction inclusion.
    async fn send_ex(&self) -> ContractResult<TrackedPendingTx<P, N>>;

    /// Call contract method (read-only)
    async fn call_ex(&self) -> ContractResult<D::CallOutput>;
}

#[allow(async_fn_in_trait)]
impl<P: ProviderEx<N>, D: CallDecoder, N: Network> CallBuilderEx<P, D, N> for CallBuilder<&P, D, N>
where
    for<'a> EthCall<'a, D, N>: IntoFuture<Output = ContractResult<D::CallOutput>>,
{
    async fn send_ex(&self) -> ContractResult<TrackedPendingTx<P, N>> {
        let tx_request = self.as_ref().clone();
        self.provider
            .send_transaction_ex(tx_request)
            .await
            .map_err(alloy::contract::Error::TransportError)
            .map_err(pretty_error)
    }

    async fn call_ex(&self) -> ContractResult<D::CallOutput> {
        self.call().await.map_err(pretty_error)
    }
}
