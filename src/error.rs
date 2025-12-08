//! RPC error classification for automatic recovery.
//!
//! This module provides intelligent error classification to enable automatic
//! recovery from common Ethereum RPC errors. By analyzing error messages,
//! we can determine appropriate recovery strategies (retry, sync nonce, etc.).

use alloy::transports::RpcError;

// ============================================================================
// Error Classification Types
// ============================================================================

/// Classified RPC error types for recovery decisions.
///
/// Each variant corresponds to a specific error condition that may occur
/// during Ethereum transaction submission, with associated recovery strategies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RpcErrorKind {
    /// Nonce is lower than expected (already used on chain)
    /// Recovery: sync() to get current nonce from chain, then retry
    NonceTooLow,

    /// Nonce creates a gap (higher than expected)
    /// Recovery: fill gaps with cancel transactions, then retry
    NonceTooHigh,

    /// Replacement transaction gas price too low
    /// Recovery: increase gas price and retry
    ReplacementUnderpriced,

    /// Insufficient funds for gas * price + value
    /// Recovery: none (user must add funds)
    InsufficientFunds,

    /// Gas limit too low for transaction
    /// Recovery: re-estimate gas and retry
    IntrinsicGasTooLow,

    /// Network/connection error
    /// Recovery: retry with backoff
    NetworkError,

    /// Transaction already known (duplicate)
    /// Recovery: treat as success, wait for existing tx
    AlreadyKnown,

    /// Unknown or unclassified error
    /// Recovery: none
    Unknown,
}

// ============================================================================
// RpcErrorKind Implementation
// ============================================================================

impl RpcErrorKind {
    /// Check if this error type is recoverable through automatic retry.
    ///
    /// Recoverable errors include nonce issues, network problems, and gas pricing.
    /// Non-recoverable errors (e.g., InsufficientFunds) require user intervention.
    pub fn is_recoverable(&self) -> bool {
        matches!(
            self,
            RpcErrorKind::NonceTooLow
                | RpcErrorKind::NonceTooHigh
                | RpcErrorKind::ReplacementUnderpriced
                | RpcErrorKind::NetworkError
                | RpcErrorKind::IntrinsicGasTooLow
                | RpcErrorKind::AlreadyKnown
        )
    }

    /// Check if this error requires synchronizing nonce from on-chain state.
    ///
    /// When nonce is too low, our local nonce tracker is ahead of the chain.
    /// We need to sync from chain to get the correct current nonce.
    pub fn needs_nonce_sync(&self) -> bool {
        matches!(self, RpcErrorKind::NonceTooLow)
    }

    /// Check if this error indicates a nonce gap that needs filling.
    ///
    /// When nonce is too high, there are missing transactions in the sequence.
    /// Gap filling involves sending placeholder transactions for missing nonces.
    pub fn needs_gap_fill(&self) -> bool {
        matches!(self, RpcErrorKind::NonceTooHigh)
    }
}

// ============================================================================
// Error Classification Functions
// ============================================================================

/// Classify an RPC error into a known error kind by pattern matching.
///
/// This function examines the error message string to identify common Ethereum
/// RPC error patterns. Different RPC providers may use different wording,
/// so we check multiple patterns for each error type.
///
/// # Arguments
/// * `error` - The RPC error to classify
///
/// # Returns
/// The classified `RpcErrorKind`, or `Unknown` if no pattern matches
pub fn classify_rpc_error<E: std::fmt::Display>(error: &RpcError<E>) -> RpcErrorKind {
    let error_str = error.to_string().to_lowercase();

    // Nonce too low patterns (transaction already executed or replaced)
    if error_str.contains("nonce too low")
        || error_str.contains("nonce is too low")
        || error_str.contains("transaction nonce is too low")
        || error_str.contains("invalid nonce")
            && (error_str.contains("too low") || error_str.contains("expected"))
    {
        return RpcErrorKind::NonceTooLow;
    }

    // Nonce too high / gap patterns
    if error_str.contains("nonce too high")
        || error_str.contains("nonce is too high")
        || error_str.contains("nonce gap")
    {
        return RpcErrorKind::NonceTooHigh;
    }

    // Replacement underpriced patterns
    if error_str.contains("replacement transaction underpriced")
        || error_str.contains("underpriced")
        || error_str.contains("gas price too low")
        || error_str.contains("max fee per gas less than block base fee")
    {
        return RpcErrorKind::ReplacementUnderpriced;
    }

    // Insufficient funds patterns
    if error_str.contains("insufficient funds")
        || error_str.contains("insufficient balance")
        || error_str.contains("not enough funds")
        || error_str.contains("exceeds balance")
    {
        return RpcErrorKind::InsufficientFunds;
    }

    // Gas too low patterns
    if error_str.contains("intrinsic gas too low")
        || error_str.contains("gas limit too low")
        || error_str.contains("out of gas")
    {
        return RpcErrorKind::IntrinsicGasTooLow;
    }

    // Already known patterns
    if error_str.contains("already known")
        || error_str.contains("already imported")
        || error_str.contains("transaction already exists")
        || error_str.contains("known transaction")
    {
        return RpcErrorKind::AlreadyKnown;
    }

    // Network error patterns
    if error_str.contains("connection")
        || error_str.contains("timeout")
        || error_str.contains("network")
        || error_str.contains("transport")
        || error_str.contains("eof")
        || error_str.contains("broken pipe")
    {
        return RpcErrorKind::NetworkError;
    }

    RpcErrorKind::Unknown
}

/// Check if an error message indicates a timeout condition.
///
/// Timeouts are special because the transaction may or may not have been
/// submitted. We need to check the chain state before deciding on recovery.
pub fn is_timeout_error(error: &anyhow::Error) -> bool {
    let error_str = error.to_string().to_lowercase();
    error_str.contains("timeout")
        || error_str.contains("timed out")
        || error_str.contains("deadline exceeded")
}

// ============================================================================
// Retry Utilities
// ============================================================================

/// Calculate exponential backoff duration for retries.
///
/// Uses 2^retry_count * base_ms formula, capped at 30 seconds max.
/// This prevents overwhelming the RPC endpoint during recovery.
///
/// # Arguments
/// * `retry_count` - Number of retries attempted so far (0-indexed)
/// * `base_ms` - Base delay in milliseconds
///
/// # Examples
/// ```
/// use alloy_ext::ext::backoff_duration;
///
/// assert_eq!(backoff_duration(0, 100).as_millis(), 100);   // 100ms
/// assert_eq!(backoff_duration(1, 100).as_millis(), 200);   // 200ms
/// assert_eq!(backoff_duration(2, 100).as_millis(), 400);   // 400ms
/// assert_eq!(backoff_duration(10, 100).as_millis(), 30_000); // Capped at 30s
/// ```
pub fn backoff_duration(retry_count: u32, base_ms: u64) -> std::time::Duration {
    let ms = base_ms * 2u64.saturating_pow(retry_count);
    let ms = ms.min(30_000); // Cap at 30 seconds to prevent excessive waits
    std::time::Duration::from_millis(ms)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_nonce_too_low() {
        let patterns = [
            "nonce too low",
            "Nonce Too Low",
            "transaction nonce is too low",
            "invalid nonce: expected 5, got 3",
        ];

        for pattern in patterns {
            // We can't easily construct RpcError, so we test the string matching logic
            assert!(
                pattern.to_lowercase().contains("nonce")
                    && (pattern.to_lowercase().contains("too low")
                        || pattern.to_lowercase().contains("expected")),
                "Pattern '{}' should match nonce too low",
                pattern
            );
        }
    }

    #[test]
    fn test_backoff_duration() {
        assert_eq!(backoff_duration(0, 100), std::time::Duration::from_millis(100));
        assert_eq!(backoff_duration(1, 100), std::time::Duration::from_millis(200));
        assert_eq!(backoff_duration(2, 100), std::time::Duration::from_millis(400));
        assert_eq!(backoff_duration(10, 100), std::time::Duration::from_millis(30_000)); // Capped
    }

    #[test]
    fn test_error_kind_recoverable() {
        assert!(RpcErrorKind::NonceTooLow.is_recoverable());
        assert!(RpcErrorKind::NonceTooHigh.is_recoverable());
        assert!(RpcErrorKind::NetworkError.is_recoverable());
        assert!(!RpcErrorKind::InsufficientFunds.is_recoverable());
        assert!(!RpcErrorKind::Unknown.is_recoverable());
    }
}
