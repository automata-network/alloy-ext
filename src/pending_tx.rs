//! Pending transaction accumulator for collecting typed events.
//!
//! This module provides `PendingTxAccum`, a utility for waiting on transactions
//! and extracting typed event data from the transaction receipt logs.
//!
//! ## Use Case
//!
//! Many smart contract interactions emit events that contain important return data.
//! For example, a `swap()` function might emit a `Swap` event with the actual amounts.
//! `PendingTxAccum` makes it easy to wait for the transaction and extract these events.
//!
//! ## Example
//!
//! ```ignore
//! // Define a result type to accumulate
//! #[derive(Default, Clone)]
//! struct SwapResult {
//!     amount_in: U256,
//!     amount_out: U256,
//! }
//!
//! // Send transaction and create accumulator
//! let tracked = provider.send_transaction_ex(swap_tx).await?;
//! let mut accum = PendingTxAccum::new(tracked, |event: PoolEvents, result| {
//!     if let PoolEvents::Swap(swap) = event {
//!         result.amount_in = swap.amount_in;
//!         result.amount_out = swap.amount_out;
//!     }
//! });
//!
//! // Wait for receipt and get accumulated result
//! let swap_result: SwapResult = accum.result().await?;
//! ```

use alloy::{
    network::{Ethereum, Network, ReceiptResponse},
    primitives::B256,
    sol_types::SolEventInterface,
};
use anyhow::anyhow;

use crate::ext::{NetworkProvider, ProviderEx, TrackedPendingTx};

// ============================================================================
// PendingTxAccum
// ============================================================================

/// A pending transaction result that accumulates typed event data into a single result.
///
/// This struct wraps a `TrackedPendingTx` and provides event accumulation functionality.
/// Nonce lifecycle management is handled entirely by `TrackedPendingTx`:
///
/// - **On `result()` success**: `TrackedPendingTx.get_receipt()` is called, which confirms the nonce.
/// - **On `Drop` without calling `result()`**: `TrackedPendingTx` is dropped, marking the nonce as abandoned.
///
/// ## Example
///
/// ```ignore
/// // Normal usage - nonce confirmed via TrackedPendingTx
/// let tracked = provider.send_transaction_ex(tx).await?;
/// let mut accum = PendingTxAccum::with_initial(tracked, (), |event, _| { ... });
/// let result = accum.result().await?;
///
/// // Fire-and-forget - nonce marked abandoned when TrackedPendingTx is dropped
/// let tracked = provider.send_transaction_ex(tx).await?;
/// drop(tracked);  // TrackedPendingTx::Drop marks nonce as ABANDONED
/// ```
pub struct PendingTxAccum<T, E, P = NetworkProvider, N = Ethereum>
where
    P: ProviderEx<N>,
    N: Network,
    T: Clone,
{
    /// The tracked pending transaction (handles nonce lifecycle)
    tracked: TrackedPendingTx<P, N>,
    /// Event handler function
    handler: Box<dyn Fn(E, &mut T) + Send>,
    /// Accumulated result
    inner: T,
}

impl<T, E, P, N> PendingTxAccum<T, E, P, N>
where
    N: Network,
    N::TxEnvelope: Clone,
    T: Clone,
    P: ProviderEx<N>,
    E: SolEventInterface,
{
    /// Create with default initial value
    pub fn new<F>(tracked: TrackedPendingTx<P, N>, f: F) -> Self
    where
        T: Default,
        F: Fn(E, &mut T) + Send + 'static,
    {
        Self::with_initial(tracked, T::default(), f)
    }

    /// Create with specified initial value.
    pub fn with_initial<F>(tracked: TrackedPendingTx<P, N>, initial: T, f: F) -> Self
    where
        F: Fn(E, &mut T) + Send + 'static,
    {
        Self {
            tracked,
            handler: Box::new(f),
            inner: initial,
        }
    }

    /// Get the transaction hash (always returns the original TX hash).
    pub fn tx_hash(&self) -> B256 {
        self.tracked.tx_hash()
    }

    /// Get the full transaction resolution with cancel fallback.
    ///
    /// This gives you complete control over handling all possible outcomes:
    /// - `Confirmed` / `OriginalConfirmedAfterCancel` - original TX was mined
    /// - `Cancelled` - cancel TX was mined instead (original TX replaced)
    /// - `Timeout` - neither TX was mined
    ///
    /// Use this when you need to handle cancellation or timeout scenarios explicitly.
    pub async fn resolution(&mut self) -> anyhow::Result<&TxResolution<N>> {
        self.tracked.resolution().await
    }

    /// Get the original transaction's receipt with cancel fallback.
    ///
    /// Only succeeds if the original transaction was confirmed.
    /// Returns error if transaction was cancelled or timed out.
    ///
    /// For full control over all outcomes, use [`resolution()`](Self::resolution) instead.
    pub async fn receipt(&mut self) -> anyhow::Result<&N::ReceiptResponse> {
        self.resolution().await?.receipt()
    }
}

impl<T, E, P> PendingTxAccum<T, E, P, Ethereum>
where
    T: Clone,
    P: ProviderEx<Ethereum>,
    E: SolEventInterface,
{
    /// Get the accumulated result from transaction events with cancel fallback.
    ///
    /// Only succeeds if the original transaction was confirmed and succeeded (not reverted).
    /// Returns error if transaction was cancelled, timed out, or reverted.
    ///
    /// For full control over all outcomes, use [`resolution()`](Self::resolution) instead.
    pub async fn result(&mut self) -> anyhow::Result<T> {
        // Get resolution and extract receipt (avoid double borrow by not calling self.receipt())
        let receipt = self.tracked.get_receipt().await?;
        if !receipt.status() {
            return Err(anyhow!(
                "Transaction reverted: {}",
                receipt.transaction_hash()
            ));
        }

        let mut inner = self.inner.clone();
        for log in receipt.logs() {
            if let Ok(event) = E::decode_raw_log(log.topics(), &log.data().data) {
                (self.handler)(event, &mut inner);
            }
        }

        Ok(inner)
    }
}

// No Drop implementation needed - TrackedPendingTx handles nonce lifecycle

/// Resolved transaction state returned by `resolution()`.
///
/// This enum represents all possible outcomes after waiting for a transaction:
/// - `Confirmed`: Original TX confirmed (happy path)
/// - `OriginalConfirmedAfterCancel`: Original TX won the race against cancel TX
/// - `Cancelled`: Cancel TX confirmed, original was replaced
/// - `Timeout`: Both TXs timed out
pub enum TxResolution<N: Network> {
    /// Original transaction confirmed (happy path)
    Confirmed {
        /// Receipt of the confirmed transaction
        receipt: N::ReceiptResponse,
    },

    /// Original TX confirmed after cancel TX was sent (cancel lost race)
    OriginalConfirmedAfterCancel {
        /// Receipt of the original transaction
        receipt: N::ReceiptResponse,
        /// Hash of the cancel TX that was sent but not mined
        cancel_tx_hash: B256,
    },

    /// Cancel TX confirmed, original was replaced
    Cancelled {
        /// Receipt of the cancel transaction (0 ETH to self)
        cancel_receipt: N::ReceiptResponse,
        /// Hash of the original TX that was replaced
        original_tx_hash: B256,
    },

    /// Both TXs timed out, nonce marked ABANDONED
    Timeout {
        /// Hash of the original transaction
        original_tx_hash: B256,
        /// Hash of the cancel transaction
        cancel_tx_hash: B256,
        /// The nonce used by both transactions
        nonce: u64,
    },
}

impl<N: Network> TxResolution<N> {
    /// Returns true if original TX was confirmed (happy path or after cancel attempt)
    #[cfg(test)]
    pub fn is_success(&self) -> bool {
        matches!(
            self,
            TxResolution::Confirmed { .. } | TxResolution::OriginalConfirmedAfterCancel { .. }
        )
    }

    /// Returns true if the transaction was cancelled
    #[cfg(test)]
    pub fn is_cancelled(&self) -> bool {
        matches!(self, TxResolution::Cancelled { .. })
    }

    /// Returns true if resolution is indeterminate (both phases timed out)
    #[cfg(test)]
    pub fn is_timeout(&self) -> bool {
        matches!(self, TxResolution::Timeout { .. })
    }

    /// Get the original transaction's receipt (if it was confirmed).
    /// Returns Err for Cancelled and Timeout states.
    pub fn receipt(&self) -> anyhow::Result<&N::ReceiptResponse> {
        match self {
            TxResolution::Confirmed { receipt } => Ok(receipt),
            TxResolution::OriginalConfirmedAfterCancel { receipt, .. } => Ok(receipt),
            TxResolution::Cancelled {
                cancel_receipt,
                original_tx_hash,
            } => Err(anyhow!(
                "Transaction {} was cancelled; cancel tx_hash: {:?}",
                original_tx_hash,
                cancel_receipt.transaction_hash()
            )),
            TxResolution::Timeout { original_tx_hash, cancel_tx_hash, nonce } => {
                Err(anyhow!("Transaction timed out without confirmation, original tx_hash: {:?}, cancel tx_hash: {:?}, nonce: {}", original_tx_hash, cancel_tx_hash, nonce))
            }
        }
    }

    /// Get the cancel transaction's receipt (if cancel was confirmed).
    /// Only returns Some for the Cancelled state.
    #[cfg(test)]
    pub fn cancel_receipt(&self) -> Option<&N::ReceiptResponse> {
        match self {
            TxResolution::Cancelled { cancel_receipt, .. } => Some(cancel_receipt),
            _ => None,
        }
    }

    /// Get cancel TX hash if one was sent
    #[cfg(test)]
    pub fn cancel_tx_hash(&self) -> Option<B256> {
        match self {
            TxResolution::OriginalConfirmedAfterCancel { cancel_tx_hash, .. } => {
                Some(*cancel_tx_hash)
            }
            TxResolution::Cancelled { .. } => None, // cancel receipt has the hash
            TxResolution::Timeout { cancel_tx_hash, .. } => Some(*cancel_tx_hash),
            TxResolution::Confirmed { .. } => None,
        }
    }
}
