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
//! - **TxState**: Enum representing transaction state (Pending/Confirmed).
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
    network::{Network, ReceiptResponse},
    primitives::{Address, B256},
    providers::{PendingTransactionBuilder, PendingTransactionError, SendableTx},
};
use tokio::time::interval;

use crate::ext::{pretty_error, AtomicNonceState, ProviderEx, StatefulNonceManager};

use super::error::{classify_rpc_error, is_timeout_error, RpcErrorKind};

/// Transaction state enum for tracking pending vs confirmed transactions.
///
/// Used internally by `TrackedPendingTx` to cache the receipt after first fetch.
pub enum TxState<N: Network> {
    /// Transaction submitted but not yet confirmed
    Pending(PendingTransactionBuilder<N>),
    /// Transaction confirmed with receipt
    Confirmed(N::ReceiptResponse),
}

impl<N: Network> TxState<N> {
    pub fn is_confirmed(&self) -> bool {
        matches!(self, TxState::Confirmed(_))
    }

    pub fn tx_hash(&self) -> B256 {
        match self {
            TxState::Pending(n) => *n.tx_hash(),
            TxState::Confirmed(r) => r.transaction_hash(),
        }
    }

    pub fn receipt(&self) -> Option<&N::ReceiptResponse> {
        match self {
            TxState::Confirmed(r) => Some(r),
            TxState::Pending(_) => None,
        }
    }

    pub async fn get_or_fetch(&mut self) -> Result<&N::ReceiptResponse, PendingTransactionError> {
        if let TxState::Pending(n) = &self {
            let provider = n.provider().clone();
            let config = n.inner().clone();
            let pending = PendingTransactionBuilder::from_config(provider, config);
            let receipt = pending.get_receipt().await?;
            *self = TxState::Confirmed(receipt);
        }

        if let TxState::Confirmed(r) = self {
            Ok(r)
        } else {
            unreachable!()
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
    /// The underlying pending transaction builder (Option for take in get_receipt)
    state: TxState<N>,
    /// The address that sent the transaction
    address: Address,
    /// The nonce used for this transaction
    nonce: u64,
    /// Atomic state handle for lock-free state transitions
    atomic_state: Arc<AtomicNonceState>,
    /// Raw signed transaction bytes for rebroadcasting
    pub(crate) raw_tx: SendableTx<N>,
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
        Self {
            provider,
            state: TxState::Pending(inner),
            address,
            nonce,
            atomic_state,
            raw_tx: filled,
        }
    }

    /// Get the transaction hash
    pub fn tx_hash(&self) -> B256 {
        self.state.tx_hash()
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

    /// Check if the transaction has been confirmed
    pub fn is_confirmed(&self) -> bool {
        self.atomic_state.is_confirmed()
    }

    /// Get the transaction receipt, confirming the nonce on success.
    ///
    /// This method:
    /// 1. Waits for the transaction to be mined
    /// 2. Periodically rebroadcasts the transaction (if enabled and raw_tx is available)
    /// 3. On success: marks the nonce as CONFIRMED and cleans up the slot
    /// 4. Returns the receipt
    ///
    /// If called multiple times, returns the cached receipt.
    ///
    /// ## Rebroadcasting
    ///
    /// When `rebroadcast` is enabled (default) and `raw_tx` is available:
    /// - The transaction is periodically rebroadcast to ensure it stays in mempool
    /// - This helps prevent transactions from being dropped due to mempool eviction
    /// - Rebroadcast interval is configurable via `RebroadcastConfig`
    ///
    /// ## Auto Recovery on Timeout
    ///
    /// When `auto_recovery` is enabled (default) and the receipt fetch times out:
    /// - The method checks if the transaction was actually mined on chain
    /// - If mined: confirms the nonce and returns the receipt
    /// - If not mined: marks the nonce as ABANDONED (will be recovered on next send)
    ///
    /// ## Error Handling
    ///
    /// If `get_receipt()` fails (network error, timeout, etc.):
    /// - With auto_recovery: checks chain state before giving up
    /// - Without auto_recovery: nonce remains PENDING, marked ABANDONED on drop
    pub async fn get_receipt(&mut self) -> anyhow::Result<&N::ReceiptResponse> {
        if self.state.is_confirmed() {
            return Ok(self.state.receipt().unwrap());
        }

        let config = self.provider.config().clone();

        // If rebroadcast is disabled or no raw_tx, use simple path
        if !config.rebroadcast.enabled {
            return self.get_receipt_simple().await;
        }

        // Rebroadcast enabled with raw_tx - use select! loop
        self.get_receipt_with_rebroadcast(config.rebroadcast.interval)
            .await
    }

    /// Simple receipt fetching without rebroadcasting
    async fn get_receipt_simple(&mut self) -> anyhow::Result<&N::ReceiptResponse> {
        match self.state.get_or_fetch().await {
            Ok(_) => {
                self.confirm_nonce().await;
            }
            Err(e) => {
                let error: anyhow::Error = e.into();

                // If auto_recovery enabled and this looks like a timeout, check chain state
                if self.provider.config().auto_recovery && is_timeout_error(&error) {
                    tracing::debug!(
                        address = %self.address,
                        nonce = self.nonce,
                        tx_hash = %self.tx_hash(),
                        "receipt timeout, checking chain state"
                    );

                    if let Some(receipt) = self.check_chain_and_recover().await? {
                        // Transaction was actually mined, update state
                        self.state = TxState::Confirmed(receipt);
                        return Ok(self.state.receipt().unwrap());
                    }
                }

                // Not recoverable or not mined
                tracing::warn!(
                    address = %self.address,
                    nonce = self.nonce,
                    tx_hash = %self.tx_hash(),
                    error = %error,
                    "failed to get receipt, nonce will be marked abandoned on drop"
                );
                return Err(error);
            }
        }

        Ok(self.state.receipt().unwrap())
    }

    /// Get receipt with periodic rebroadcasting using select!
    async fn get_receipt_with_rebroadcast(
        &mut self,
        rebroadcast_interval: Duration,
    ) -> anyhow::Result<&N::ReceiptResponse> {
        // Extract pending state components (clone to avoid borrow issues)
        let (provider_root, pending_config) = match &self.state {
            TxState::Pending(p) => (p.provider().clone(), p.inner().clone()),
            TxState::Confirmed(_) => return Ok(self.state.receipt().unwrap()),
        };

        // Create interval for rebroadcasting
        let mut rebroadcast_ticker = interval(rebroadcast_interval);
        rebroadcast_ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        // Skip the first immediate tick
        rebroadcast_ticker.tick().await;

        // Build the receipt future using cloned components
        let receipt_fut = async {
            PendingTransactionBuilder::from_config(provider_root, pending_config)
                .get_receipt()
                .await
        };
        tokio::pin!(receipt_fut);

        loop {
            tokio::select! {
                // Branch 1: Receipt returned (success or error)
                result = &mut receipt_fut => {
                    match result {
                        Ok(receipt) => {
                            self.state = TxState::Confirmed(receipt);
                            self.confirm_nonce().await;
                            return Ok(self.state.receipt().unwrap());
                        }
                        Err(e) => {
                            let error: anyhow::Error = e.into();

                            // If auto_recovery enabled and this looks like a timeout, check chain state
                            if self.provider.config().auto_recovery && is_timeout_error(&error) {
                                tracing::debug!(
                                    address = %self.address,
                                    nonce = self.nonce,
                                    tx_hash = %self.tx_hash(),
                                    "receipt timeout, checking chain state"
                                );

                                if let Some(receipt) = self.check_chain_and_recover().await? {
                                    self.state = TxState::Confirmed(receipt);
                                    return Ok(self.state.receipt().unwrap());
                                }
                            }

                            tracing::warn!(
                                address = %self.address,
                                nonce = self.nonce,
                                tx_hash = %self.tx_hash(),
                                error = %error,
                                "failed to get receipt, nonce will be marked abandoned on drop"
                            );
                            return Err(error);
                        }
                    }
                }

                // Branch 2: Rebroadcast interval tick
                _ = rebroadcast_ticker.tick() => {
                    self.rebroadcast().await;
                }
            }
        }
    }

    /// Rebroadcast the signed transaction to the network
    async fn rebroadcast(&self) {
        let raw_tx = self.raw_tx.clone();

        match self.provider.send_transaction_inner(raw_tx).await {
            Ok(_) => {
                tracing::debug!(
                    address = %self.address,
                    nonce = self.nonce,
                    tx_hash = %self.tx_hash(),
                    "rebroadcast successful"
                );
            }
            Err(e) => {
                let kind = classify_rpc_error(&e);
                match kind {
                    RpcErrorKind::AlreadyKnown => {
                        // Good - still in mempool
                        tracing::trace!(
                            address = %self.address,
                            nonce = self.nonce,
                            tx_hash = %self.tx_hash(),
                            "rebroadcast: tx still in mempool"
                        );
                    }
                    RpcErrorKind::NonceTooLow => {
                        // Nonce already used - tx might be mined
                        tracing::debug!(
                            address = %self.address,
                            nonce = self.nonce,
                            tx_hash = %self.tx_hash(),
                            "rebroadcast: nonce already used, tx may be mined"
                        );
                    }
                    _ => {
                        tracing::warn!(
                            address = %self.address,
                            nonce = self.nonce,
                            tx_hash = %self.tx_hash(),
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

    /// Internal: check chain state on timeout and attempt recovery
    ///
    /// Returns Some(receipt) if the transaction was actually mined, None otherwise.
    async fn check_chain_and_recover(&mut self) -> anyhow::Result<Option<N::ReceiptResponse>> {
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
