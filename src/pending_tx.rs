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
    network::{Ethereum, Network},
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

impl<T, E, P> PendingTxAccum<T, E, P, Ethereum>
where
    T: Clone,
    P: ProviderEx<Ethereum>,
    E: SolEventInterface,
{
    /// Create with default initial value
    pub fn new<F>(tracked: TrackedPendingTx<P, Ethereum>, f: F) -> Self
    where
        T: Default,
        F: Fn(E, &mut T) + Send + 'static,
    {
        Self::with_initial(tracked, T::default(), f)
    }

    /// Create with specified initial value.
    pub fn with_initial<F>(tracked: TrackedPendingTx<P, Ethereum>, initial: T, f: F) -> Self
    where
        F: Fn(E, &mut T) + Send + 'static,
    {
        Self {
            tracked,
            handler: Box::new(f),
            inner: initial,
        }
    }

    /// Get the transaction hash
    pub fn tx_hash(&self) -> B256 {
        self.tracked.tx_hash()
    }

    /// Get the transaction receipt.
    ///
    /// This calls `TrackedPendingTx.get_receipt()` which automatically confirms the nonce.
    pub async fn receipt(&mut self) -> anyhow::Result<&<Ethereum as Network>::ReceiptResponse> {
        self.tracked.get_receipt().await
    }

    /// Get the accumulated result from transaction events.
    ///
    /// This calls `TrackedPendingTx.get_receipt()` which automatically confirms the nonce.
    pub async fn result(&mut self) -> anyhow::Result<T> {
        let receipt = self.tracked.get_receipt().await?;

        // Now we can safely access other fields
        if !receipt.status() {
            return Err(anyhow!("transaction failed: {:?}", receipt.status()));
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
