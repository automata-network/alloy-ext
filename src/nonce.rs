//! Stateful nonce manager with atomic state transitions.
//!
//! This module provides a production-grade nonce management solution that solves
//! common problems with Ethereum transaction nonce handling:
//!
//! ## Problem Statement
//!
//! Ethereum transactions must have sequential nonces. If transaction #5 is dropped
//! (not mined), transaction #6 will be stuck forever. This module tracks nonce
//! lifecycle to detect and recover from such situations.
//!
//! ## Architecture
//!
//! - **Lock-free State Updates**: Uses `AtomicU8` for state transitions, enabling
//!   efficient updates from `Drop` implementations without blocking.
//! - **Per-Account State**: Each address has independent nonce tracking.
//! - **BTreeMap for Ordering**: Slots are stored in a BTreeMap for ordered iteration
//!   (important for gap detection).
//!
//! ## State Machine
//!
//! ```text
//!   RESERVED ──► PENDING ──► CONFIRMED
//!                   │
//!                   └──► ABANDONED (needs gap filling)
//! ```

use std::{
    collections::BTreeMap,
    sync::{
        atomic::{AtomicU8, Ordering},
        Arc,
    },
    time::Instant,
};

use alloy::{
    network::Network,
    primitives::{Address, B256},
    providers::{fillers::NonceManager, Provider},
    transports::TransportResult,
};
use async_trait::async_trait;
use dashmap::DashMap;
use tokio::sync::Mutex;
use tracing::trace;

// ============================================================================
// Atomic Nonce State (for lock-free status updates)
// ============================================================================

/// Atomic state constants for NonceSlot.
///
/// These values are used with `AtomicU8` for lock-free state transitions.
/// The numeric values are chosen to be dense for efficient comparison.
pub mod nonce_state {
    /// Nonce is reserved but transaction not yet sent to RPC
    pub const RESERVED: u8 = 0;
    /// Transaction sent to RPC, waiting for confirmation
    pub const PENDING: u8 = 1;
    /// Transaction dropped without confirmation (may create gap)
    pub const ABANDONED: u8 = 2;
    /// Transaction confirmed in a block
    pub const CONFIRMED: u8 = 3;
}

/// Shared atomic state for a nonce slot.
///
/// This allows lock-free updates from Drop implementations.
/// The caller holds an `Arc<AtomicNonceState>` and can atomically
/// transition the state without acquiring the nonce manager's lock.
#[derive(Debug)]
pub struct AtomicNonceState {
    state: AtomicU8,
}

impl AtomicNonceState {
    /// Create a new atomic state in RESERVED state.
    pub fn new_reserved() -> Self {
        Self {
            state: AtomicU8::new(nonce_state::RESERVED),
        }
    }

    /// Get the current state with Acquire ordering.
    ///
    /// Acquire ensures we see all writes that happened before the store.
    pub fn get(&self) -> u8 {
        self.state.load(Ordering::Acquire)
    }

    /// Atomically transition: PENDING → ABANDONED.
    ///
    /// Uses compare-and-swap (CAS) to ensure only valid transitions.
    /// This is safe to call from Drop without holding any locks.
    ///
    /// Returns `true` if the transition was successful.
    pub fn mark_abandoned(&self) -> bool {
        self.state
            .compare_exchange(
                nonce_state::PENDING,
                nonce_state::ABANDONED,
                Ordering::AcqRel,  // Acquire on success, Release the new value
                Ordering::Acquire, // Acquire on failure to see current value
            )
            .is_ok()
    }

    /// Atomically transition: RESERVED → PENDING.
    ///
    /// Called when transaction is successfully sent to RPC.
    /// Returns `true` if the transition was successful.
    pub fn mark_pending(&self) -> bool {
        self.state
            .compare_exchange(
                nonce_state::RESERVED,
                nonce_state::PENDING,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_ok()
    }

    /// Unconditionally set state to CONFIRMED.
    ///
    /// This is an unconditional store because confirmation is terminal
    /// and can happen from any state (e.g., if we confirm an abandoned tx).
    pub fn mark_confirmed(&self) {
        self.state.store(nonce_state::CONFIRMED, Ordering::Release);
    }

    /// Check if state is ABANDONED.
    pub fn is_abandoned(&self) -> bool {
        self.get() == nonce_state::ABANDONED
    }

    /// Check if state is CONFIRMED.
    pub fn is_confirmed(&self) -> bool {
        self.get() == nonce_state::CONFIRMED
    }
}

// ============================================================================
// Nonce Slot States
// ============================================================================

/// State of a nonce slot in the nonce manager.
///
/// ## Lifecycle
///
/// ```text
///                        send success
///   get_next_nonce() ─────────► mark_sent() ────► confirm()
///        │                                  │                      │
///        ▼                                  ▼                      ▼
///    Reserved ─────────────► Pending ──────► Cleared
///        │                                  │
///        │ send failure                     │ dropped without confirm
///        ▼                                  ▼
///    release() ◄──────────── Abandoned
///        │                                  │
///        ▼                                  ▼
///    Released                         Needs gap filling
///   (reusable)                       (send cancel tx)
/// ```
///
/// Each slot contains an `Arc<AtomicNonceState>` that can be shared with
/// transaction handlers, allowing lock-free state transitions from Drop.
#[derive(Debug, Clone)]
pub struct NonceSlot {
    /// Shared atomic state for lock-free updates
    pub atomic_state: Arc<AtomicNonceState>,
    /// Transaction hash (set when transitioning to Pending)
    pub tx_hash: Option<B256>,
    /// Timestamp when slot was created/reserved
    pub reserved_at: Instant,
    /// Timestamp when transaction was sent (if applicable)
    pub sent_at: Option<Instant>,
}

impl NonceSlot {
    /// Create a new reserved slot
    pub fn new_reserved() -> (Self, Arc<AtomicNonceState>) {
        let atomic_state = Arc::new(AtomicNonceState::new_reserved());
        let slot = Self {
            atomic_state: Arc::clone(&atomic_state),
            tx_hash: None,
            reserved_at: Instant::now(),
            sent_at: None,
        };
        (slot, atomic_state)
    }

    /// Check if slot is in Reserved state
    pub fn is_reserved(&self) -> bool {
        self.atomic_state.get() == nonce_state::RESERVED
    }

    /// Check if slot is in Pending state
    pub fn is_pending(&self) -> bool {
        self.atomic_state.get() == nonce_state::PENDING
    }

    /// Check if slot is in Abandoned state
    pub fn is_abandoned(&self) -> bool {
        self.atomic_state.is_abandoned()
    }

    /// Check if slot is in Confirmed state
    pub fn is_confirmed(&self) -> bool {
        self.atomic_state.is_confirmed()
    }

    /// Get the current state as u8
    pub fn state(&self) -> u8 {
        self.atomic_state.get()
    }
}

// ============================================================================
// Account Nonce State (internal)
// ============================================================================

/// Internal state for a single account's nonces
#[derive(Debug)]
struct AccountNonceState {
    /// The confirmed on-chain nonce (next available from chain's perspective)
    base_nonce: u64,
    /// The next nonce to allocate
    next_nonce: u64,
    /// Active nonce slots (nonce -> state)
    slots: BTreeMap<u64, NonceSlot>,
}

// ============================================================================
// Nonce Status (public snapshot)
// ============================================================================

/// Snapshot of nonce state for monitoring/debugging.
///
/// Use `StatefulNonceManager::get_status()` to obtain this snapshot.
#[derive(Debug, Clone)]
pub struct NonceStatus {
    /// The confirmed on-chain nonce (next available from chain's perspective)
    pub base_nonce: u64,
    /// The next nonce to allocate locally
    pub next_nonce: u64,
    /// List of nonces in Reserved or Pending state
    pub pending_nonces: Vec<u64>,
    /// List of nonces in Abandoned state
    pub abandoned_nonces: Vec<u64>,
}

impl NonceStatus {
    /// Get the count of pending nonces
    pub fn pending_count(&self) -> usize {
        self.pending_nonces.len()
    }

    /// Get the count of abandoned nonces
    pub fn abandoned_count(&self) -> usize {
        self.abandoned_nonces.len()
    }

    pub fn confirmed(&self, nonce: u64) -> bool {
        !self.pending_nonces.contains(&nonce) && !self.abandoned_nonces.contains(&nonce)
    }
}

// ============================================================================
// StatefulNonceManager
// ============================================================================

/// A stateful nonce manager that tracks nonce lifecycle.
///
/// Implements alloy's `NonceManager` trait for compatibility with `NonceFiller`,
/// while providing additional methods for managing nonce state:
///
/// ## State Transitions
///
/// - `get_next_nonce()`: Allocate nonce → `Reserved`
/// - `mark_sent()`: `Reserved` → `Pending` (after successful RPC send)
/// - `confirm()`: `Pending` → cleared (after receipt confirmation)
/// - `release()`: `Reserved` → cleared (on send failure, nonce can be reused)
/// - `mark_abandoned()`: `Pending` → `Abandoned` (caller dropped without confirm)
///
/// ## Gap Filling
///
/// When a nonce is abandoned, it may create a gap that blocks subsequent transactions.
/// Use `get_abandoned_nonces()` to get the list of abandoned nonces, then fill them
/// with cancel transactions (0 ETH to self with higher gas price).
///
/// ## Sync
///
/// - `sync()`: Re-sync with on-chain state, clearing all local state
/// - `get_status()`: Get current state snapshot for monitoring
#[derive(Clone, Debug, Default)]
pub struct StatefulNonceManager {
    /// Per-address state, protected by Arc<Mutex> for thread safety
    states: Arc<DashMap<Address, Arc<Mutex<AccountNonceState>>>>,
}

impl StatefulNonceManager {
    /// Create a new stateful nonce manager
    pub fn new() -> Self {
        Self {
            states: Arc::new(DashMap::new()),
        }
    }

    /// Mark a nonce as sent (caller should call after sending transaction)
    ///
    /// This updates both the atomic state (lock-free) and the slot metadata (with lock).
    pub async fn mark_sent(&self, address: Address, nonce: u64, tx_hash: B256) {
        if let Some(state_arc) = self.states.get(&address) {
            let mut state = state_arc.lock().await;
            if let Some(slot) = state.slots.get_mut(&nonce) {
                // Atomically transition from Reserved to Pending
                if slot.atomic_state.mark_pending() {
                    slot.tx_hash = Some(tx_hash);
                    slot.sent_at = Some(Instant::now());
                    trace!(%address, nonce, %tx_hash, "marked nonce as sent");
                }
            }
        }
    }

    /// Confirm a nonce has been successfully included in a block.
    ///
    /// This clears all slots with nonce <= the confirmed nonce, including any
    /// abandoned nonces before this one (they must have been mined too).
    ///
    /// Also marks the atomic state as CONFIRMED for any holders of the Arc.
    pub async fn confirm(&self, address: Address, nonce: u64) {
        if let Some(state_arc) = self.states.get(&address) {
            let mut state = state_arc.lock().await;
            state.base_nonce = nonce + 1;
            // Mark confirmed and remove all slots <= confirmed nonce
            state.slots.retain(|&n, slot| {
                if n <= nonce {
                    slot.atomic_state.mark_confirmed();
                    false
                } else {
                    true
                }
            });
            trace!(%address, nonce, new_base = state.base_nonce, "confirmed nonce");
        }
    }

    /// Mark a nonce as abandoned.
    ///
    /// **DEPRECATED**: Prefer using `AtomicNonceState::mark_abandoned()` directly
    /// from the `Arc<AtomicNonceState>` returned by `get_next_nonce_ex()` or
    /// stored in `TrackedPendingTx`. This allows lock-free abandonment from Drop.
    ///
    /// This async version is kept for compatibility and for cases where you need
    /// to log the abandonment with the nonce manager's context.
    ///
    /// Called when the caller drops `PendingTxAccum` or `TrackedPendingTx` without
    /// waiting for confirmation. The transaction may or may not be on-chain.
    ///
    /// If this nonce is not on-chain and there are higher nonces that need to be
    /// submitted, we need to fill this gap with a cancel transaction.
    pub async fn mark_abandoned(&self, address: Address, nonce: u64) {
        if let Some(state_arc) = self.states.get(&address) {
            let state = state_arc.lock().await;
            if let Some(slot) = state.slots.get(&nonce) {
                // Atomically transition from Pending to Abandoned
                if slot.atomic_state.mark_abandoned() {
                    if let Some(tx_hash) = slot.tx_hash {
                        trace!(%address, nonce, %tx_hash, "marked nonce as abandoned");
                    } else {
                        trace!(%address, nonce, "marked nonce as abandoned");
                    }
                }
            }
        }
    }

    /// Get the list of abandoned nonces that may need gap filling.
    ///
    /// Returns a list of (nonce, tx_hash) pairs for all abandoned nonces.
    /// The caller should check if these transactions are on-chain:
    /// - If on-chain: call `confirm(nonce)` to clear
    /// - If not on-chain: send a cancel transaction to fill the gap
    pub async fn get_abandoned_nonces(&self, address: Address) -> Vec<(u64, B256)> {
        if let Some(state_arc) = self.states.get(&address) {
            let state = state_arc.lock().await;
            return state
                .slots
                .iter()
                .filter_map(|(&nonce, slot)| {
                    if slot.is_abandoned() {
                        slot.tx_hash.map(|tx_hash| (nonce, tx_hash))
                    } else {
                        None
                    }
                })
                .collect();
        }
        vec![]
    }

    /// Release an unused nonce (e.g., transaction expired before sending).
    ///
    /// Returns a list of nonces that need gap-filling if releasing creates holes.
    /// If the released nonce is the last allocated one, next_nonce is decremented.
    pub async fn release(&self, address: Address, nonce: u64) -> Vec<u64> {
        if let Some(state_arc) = self.states.get(&address) {
            let mut state = state_arc.lock().await;
            state.slots.remove(&nonce);
            trace!(%address, nonce, "released nonce");

            // Check if this creates a gap
            if nonce < state.next_nonce - 1 {
                // Return all nonces after this one that need gap filling
                return state
                    .slots
                    .keys()
                    .filter(|&&n| n > nonce)
                    .copied()
                    .collect();
            }

            // If this was the last allocated nonce, we can reuse it
            if nonce == state.next_nonce - 1 {
                state.next_nonce = nonce;
            }
        }
        vec![]
    }

    /// Re-sync with on-chain state.
    /// Clears all local state and fetches the current nonce from the chain.
    pub async fn sync<P, N>(&self, provider: &P, address: Address) -> TransportResult<()>
    where
        P: Provider<N>,
        N: Network,
    {
        let on_chain_nonce = provider.get_transaction_count(address).await?;

        let state_arc = {
            let entry = self.states.entry(address).or_insert_with(|| {
                Arc::new(Mutex::new(AccountNonceState {
                    base_nonce: on_chain_nonce,
                    next_nonce: on_chain_nonce,
                    slots: BTreeMap::new(),
                }))
            });
            Arc::clone(entry.value())
        };

        let mut state = state_arc.lock().await;
        state.base_nonce = on_chain_nonce;
        state.next_nonce = on_chain_nonce;
        state.slots.clear();
        trace!(%address, on_chain_nonce, "synced nonce from chain");

        Ok(())
    }

    /// Get the atomic state handle for a specific nonce slot.
    ///
    /// Returns `None` if the slot doesn't exist.
    pub async fn get_slot_atomic_state(
        &self,
        address: Address,
        nonce: u64,
    ) -> Option<Arc<AtomicNonceState>> {
        if let Some(state_arc) = self.states.get(&address) {
            let state = state_arc.lock().await;
            if let Some(slot) = state.slots.get(&nonce) {
                return Some(Arc::clone(&slot.atomic_state));
            }
        }
        None
    }

    /// Get current state snapshot for monitoring/debugging.
    ///
    /// Returns `None` if the address has never been used with this manager.
    pub async fn get_status(&self, address: Address) -> Option<NonceStatus> {
        if let Some(state_arc) = self.states.get(&address) {
            let state = state_arc.lock().await;

            let mut pending_nonces = Vec::new();
            let mut abandoned_nonces = Vec::new();

            for (&nonce, slot) in &state.slots {
                let slot_state = slot.state();
                if slot_state == nonce_state::RESERVED || slot_state == nonce_state::PENDING {
                    pending_nonces.push(nonce);
                } else if slot_state == nonce_state::ABANDONED {
                    abandoned_nonces.push(nonce);
                }
            }

            return Some(NonceStatus {
                base_nonce: state.base_nonce,
                next_nonce: state.next_nonce,
                pending_nonces,
                abandoned_nonces,
            });
        }
        None
    }

    /// Get or initialize account state (internal helper)
    async fn get_or_init_state<P, N>(
        &self,
        provider: &P,
        address: Address,
    ) -> TransportResult<Arc<Mutex<AccountNonceState>>>
    where
        P: Provider<N>,
        N: Network,
    {
        // Fast path: already exists
        if let Some(state) = self.states.get(&address) {
            return Ok(Arc::clone(state.value()));
        }

        // Slow path: need to fetch from chain
        let on_chain_nonce = provider.get_transaction_count(address).await?;
        trace!(%address, on_chain_nonce, "initialized nonce from chain");

        let entry = self.states.entry(address).or_insert_with(|| {
            Arc::new(Mutex::new(AccountNonceState {
                base_nonce: on_chain_nonce,
                next_nonce: on_chain_nonce,
                slots: BTreeMap::new(),
            }))
        });

        Ok(Arc::clone(entry.value()))
    }
}

// ============================================================================
// NonceManager trait implementation
// ============================================================================

#[cfg_attr(target_family = "wasm", async_trait(?Send))]
#[cfg_attr(not(target_family = "wasm"), async_trait)]
impl NonceManager for StatefulNonceManager {
    async fn get_next_nonce<P, N>(&self, provider: &P, address: Address) -> TransportResult<u64>
    where
        P: Provider<N>,
        N: Network,
    {
        // Get or initialize account state
        let state_arc = self.get_or_init_state(provider, address).await?;
        let mut state = state_arc.lock().await;

        // Allocate the next nonce with atomic state
        let nonce = state.next_nonce;
        let (slot, _atomic_state) = NonceSlot::new_reserved();
        state.slots.insert(nonce, slot);
        state.next_nonce += 1;

        trace!(%address, nonce, next = state.next_nonce, "allocated nonce");

        Ok(nonce)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_nonce_slot_lifecycle() {
        let manager = StatefulNonceManager::new();
        let address = Address::ZERO;

        // Simulate getting nonces (without provider, we'll manually set state)
        {
            let entry = manager.states.entry(address).or_insert_with(|| {
                Arc::new(Mutex::new(AccountNonceState {
                    base_nonce: 5,
                    next_nonce: 5,
                    slots: BTreeMap::new(),
                }))
            });
            let mut state = entry.value().lock().await;
            let (slot, _) = NonceSlot::new_reserved();
            state.slots.insert(5, slot);
            state.next_nonce = 6;
        }

        // Mark as sent
        let tx_hash = B256::ZERO;
        manager.mark_sent(address, 5, tx_hash).await;

        // Check status
        let status = manager.get_status(address).await.unwrap();
        assert_eq!(status.base_nonce, 5);
        assert_eq!(status.next_nonce, 6);
        assert_eq!(status.pending_count(), 1);
        assert_eq!(status.pending_nonces, vec![5]);
        assert_eq!(status.abandoned_count(), 0);
        assert!(status.abandoned_nonces.is_empty());

        // Confirm
        manager.confirm(address, 5).await;

        // Check status after confirm
        let status = manager.get_status(address).await.unwrap();
        assert_eq!(status.base_nonce, 6);
        assert_eq!(status.pending_count(), 0);
        assert_eq!(status.abandoned_count(), 0);
    }

    #[tokio::test]
    async fn test_release_nonce() {
        let manager = StatefulNonceManager::new();
        let address = Address::ZERO;

        // Setup: nonces 5, 6, 7 allocated
        {
            let entry = manager.states.entry(address).or_insert_with(|| {
                Arc::new(Mutex::new(AccountNonceState {
                    base_nonce: 5,
                    next_nonce: 8,
                    slots: BTreeMap::new(),
                }))
            });
            let mut state = entry.value().lock().await;
            for nonce in 5..8 {
                let (slot, _) = NonceSlot::new_reserved();
                state.slots.insert(nonce, slot);
            }
        }

        // Release nonce 6 (creates gap)
        let gaps = manager.release(address, 6).await;
        assert_eq!(gaps, vec![7]); // nonce 7 needs gap filling

        // Release nonce 7 (last one, can decrement)
        let gaps = manager.release(address, 7).await;
        assert!(gaps.is_empty());

        let status = manager.get_status(address).await.unwrap();
        assert_eq!(status.next_nonce, 7); // decremented
    }

    #[tokio::test]
    async fn test_abandoned_nonce() {
        let manager = StatefulNonceManager::new();
        let address = Address::ZERO;
        let tx_hash = B256::ZERO;

        // Setup: nonce 5 in Pending state (Reserved -> mark_pending -> Pending)
        let atomic_state = {
            let entry = manager.states.entry(address).or_insert_with(|| {
                Arc::new(Mutex::new(AccountNonceState {
                    base_nonce: 5,
                    next_nonce: 6,
                    slots: BTreeMap::new(),
                }))
            });
            let mut state = entry.value().lock().await;
            let (mut slot, atomic_state) = NonceSlot::new_reserved();
            // Manually transition to Pending
            atomic_state.mark_pending();
            slot.tx_hash = Some(tx_hash);
            slot.sent_at = Some(Instant::now());
            state.slots.insert(5, slot);
            atomic_state
        };

        // Mark as abandoned using atomic state (simulates lock-free Drop)
        assert!(atomic_state.mark_abandoned());

        // Check status
        let status = manager.get_status(address).await.unwrap();
        assert_eq!(status.pending_count(), 0);
        assert_eq!(status.abandoned_count(), 1);
        assert_eq!(status.abandoned_nonces, vec![5]);

        // Get abandoned nonces
        let abandoned = manager.get_abandoned_nonces(address).await;
        assert_eq!(abandoned.len(), 1);
        assert_eq!(abandoned[0], (5, tx_hash));

        // Confirm clears abandoned too
        manager.confirm(address, 5).await;
        let status = manager.get_status(address).await.unwrap();
        assert_eq!(status.abandoned_count(), 0);
        assert_eq!(status.base_nonce, 6);
    }

    #[tokio::test]
    async fn test_atomic_state_lock_free() {
        // Test that atomic state can be modified without holding any locks
        let (slot, atomic_state) = NonceSlot::new_reserved();

        // Initial state is Reserved
        assert!(slot.is_reserved());
        assert_eq!(atomic_state.get(), nonce_state::RESERVED);

        // Transition to Pending
        assert!(atomic_state.mark_pending());
        assert!(slot.is_pending());
        assert!(!atomic_state.mark_pending()); // Can't transition again

        // Transition to Abandoned
        assert!(atomic_state.mark_abandoned());
        assert!(slot.is_abandoned());
        assert!(!atomic_state.mark_abandoned()); // Can't transition again

        // Mark confirmed (unconditional)
        atomic_state.mark_confirmed();
        assert!(slot.is_confirmed());
    }
}
