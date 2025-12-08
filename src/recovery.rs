//! Nonce recovery and gap filling logic.
//!
//! This module provides automatic recovery for abandoned nonces that may block
//! subsequent transactions. When a nonce is marked as abandoned (e.g., transaction
//! dropped from mempool or timeout), it creates a "gap" that prevents higher nonces
//! from being mined.
//!
//! ## Recovery Process
//!
//! 1. Get list of abandoned nonces via `get_abandoned_nonces()`
//! 2. For each abandoned nonce (in order):
//!    - Check if the original transaction was actually mined
//!    - If mined: call `confirm()` to clear the slot
//!    - If not mined: send a "cancel" transaction (0 ETH to self) to fill the gap
//! 3. Once gaps are filled, subsequent pending transactions can be mined
//!
//! ## Usage
//!
//! Recovery is automatically triggered when `auto_recovery` is enabled (default):
//!
//! - On `send_transaction_ex()` when nonce errors are detected
//! - On `get_receipt()` timeout
//! - Manually via `provider.recover(address)`

use alloy::primitives::{Address, B256};

// ============================================================================
// Recovery Result Types
// ============================================================================

/// Result of a single nonce recovery attempt.
///
/// Each abandoned nonce can have one of three outcomes:
/// - Already mined (just needed confirmation update)
/// - Gap filled with cancel transaction
/// - Failed to recover
#[derive(Debug, Clone)]
pub enum SingleRecoveryResult {
    /// Original transaction was already mined on chain.
    /// The nonce slot was confirmed without needing a cancel transaction.
    AlreadyMined {
        nonce: u64,
        original_tx_hash: B256,
    },
    /// Gap was filled by sending a cancel transaction (0 ETH to self).
    /// Both hashes are provided for tracking purposes.
    GapFilled {
        nonce: u64,
        /// Hash of the original abandoned transaction
        original_tx_hash: B256,
        /// Hash of the cancel transaction that filled the gap
        cancel_tx_hash: B256,
    },
    /// Recovery failed for this nonce.
    /// The error message provides details on what went wrong.
    Failed {
        nonce: u64,
        original_tx_hash: B256,
        error: String,
    },
}

impl SingleRecoveryResult {
    /// Get the nonce that this result is for.
    pub fn nonce(&self) -> u64 {
        match self {
            SingleRecoveryResult::AlreadyMined { nonce, .. } => *nonce,
            SingleRecoveryResult::GapFilled { nonce, .. } => *nonce,
            SingleRecoveryResult::Failed { nonce, .. } => *nonce,
        }
    }

    /// Check if recovery was successful (either mined or gap filled).
    pub fn is_success(&self) -> bool {
        matches!(
            self,
            SingleRecoveryResult::AlreadyMined { .. } | SingleRecoveryResult::GapFilled { .. }
        )
    }
}

/// Result of recovering all abandoned nonces for an address.
///
/// Contains aggregate statistics and detailed results for each recovered nonce.
/// Used by `NetworkProvider::recover()` to report recovery outcomes.
#[derive(Debug, Clone, Default)]
pub struct RecoveryResult {
    /// Address that was recovered
    pub address: Address,
    /// Number of nonces successfully recovered (mined or gap-filled)
    pub recovered_count: usize,
    /// Number of nonces that failed to recover
    pub failed_count: usize,
    /// Detailed results for each nonce (in processing order)
    pub results: Vec<SingleRecoveryResult>,
}

impl RecoveryResult {
    pub fn new(address: Address) -> Self {
        Self {
            address,
            recovered_count: 0,
            failed_count: 0,
            results: Vec::new(),
        }
    }

    pub fn add_result(&mut self, result: SingleRecoveryResult) {
        if result.is_success() {
            self.recovered_count += 1;
        } else {
            self.failed_count += 1;
        }
        self.results.push(result);
    }

    pub fn is_fully_recovered(&self) -> bool {
        self.failed_count == 0
    }

    pub fn has_any_recovery(&self) -> bool {
        self.recovered_count > 0
    }
}

// ============================================================================
// Recovery Options
// ============================================================================

/// Options for recovery operations.
///
/// Configure how `NetworkProvider::recover_with_options()` behaves.
#[derive(Debug, Clone)]
pub struct RecoveryOptions {
    /// Gas price multiplier for cancel transactions (default: 1.1).
    /// Must be > 1.0 to replace the original transaction in mempool.
    pub gas_multiplier: f64,
    /// Maximum number of nonces to recover in one call (default: 10).
    /// Limits the number of cancel transactions sent in a single recovery.
    pub max_nonces: usize,
    /// Whether to continue recovering subsequent nonces after a failure (default: true).
    /// If false, recovery stops at the first failed nonce.
    pub continue_on_failure: bool,
}

impl Default for RecoveryOptions {
    fn default() -> Self {
        Self {
            gas_multiplier: 1.1,
            max_nonces: 10,
            continue_on_failure: true,
        }
    }
}

impl RecoveryOptions {
    pub fn with_gas_multiplier(mut self, multiplier: f64) -> Self {
        self.gas_multiplier = multiplier;
        self
    }

    pub fn with_max_nonces(mut self, max: usize) -> Self {
        self.max_nonces = max;
        self
    }

    pub fn with_continue_on_failure(mut self, continue_on_failure: bool) -> Self {
        self.continue_on_failure = continue_on_failure;
        self
    }
}
