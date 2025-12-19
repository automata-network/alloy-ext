//! # alloy-ext
//!
//! Production-grade Ethereum transaction management library extending Alloy.
//!
//! ## Core Features
//!
//! - **Nonce Lifecycle Management**: Atomic state machine tracking (Reserved → Pending → Confirmed/Abandoned)
//! - **Automatic Error Recovery**: Handles nonce errors, network timeouts with exponential backoff
//! - **Transaction Rebroadcasting**: Periodic resending to prevent mempool eviction
//! - **Contract Error Parsing**: Distributed registry pattern for Solidity revert decoding
//! - **RPC Error Classification**: Intelligent error categorization for recovery decisions
//!
//! ## Usage
//!
//! ```ignore
//! use alloy_ext::ext::*;
//!
//! let provider = ProviderBuilder::new()
//!     .connect_http(rpc_url)
//!     .with_signer(signer);
//! ```

// ============================================================================
// Internal Module Declarations
// ============================================================================

/// Transaction call builder wrapping TrackedPendingTx for automatic nonce confirmation
mod call_builder;

/// Contract error parser registry for decoding Solidity revert errors
mod contract_error;

/// RPC error classification and wrapper types
mod error;

/// Gas pricing utilities for transaction replacement
mod gas;

/// Stateful nonce manager with atomic state transitions for nonce lifecycle tracking
mod nonce;

/// Pending transaction accumulator for collecting typed events from tx logs
mod pending_tx;

/// Extended network provider with auto-recovery and rebroadcast capabilities
mod provider;

/// Recovery operation result types
mod recovery;

/// Test harness module (compiled only in test mode)
#[cfg(test)]
pub mod test_harness;

// ============================================================================
// Public Exports
// ============================================================================

/// Re-export all public APIs from the alloy crate.
/// Users can access full alloy functionality directly through alloy_ext.
pub use alloy::*;

/// Internal module for macro usage.
/// Note: Module name is intentionally "__privite" for backward compatibility.
pub mod __privite {
    /// inventory crate - distributed plugin registration for contract error parsers
    pub use inventory;
    /// paste crate - identifier concatenation in macros
    pub use paste;
}

/// Extension module containing all advanced features:
///
/// - `NetworkProvider` - Provider with auto-recovery
/// - `StatefulNonceManager` - Stateful nonce manager
/// - `TrackedPendingTx` - Pending tx with nonce confirmation tracking
/// - `PendingTxAccum` - Transaction event accumulator
/// - `ContractErrorParser` - Contract error parser trait
/// - `RpcErrorExt` - RPC error classification trait
pub mod ext {
    pub use super::call_builder::*;
    pub use super::contract_error::*;
    pub use super::error::*;
    pub use super::gas::*;
    pub use super::nonce::*;
    pub use super::pending_tx::*;
    pub use super::provider::*;
    pub use super::recovery::*;
}

/// Define contract stubs and automatically register error parsers.
///
/// This macro generates `alloy::sol!` definitions for each contract and
/// automatically registers their error types with the global error registry.
///
/// # Example
///
/// ```ignore
/// use alloy_ext::contract;
///
/// contract! {
///     OrderBook => "out/OrderBook.sol/OrderBook.json",
/// }
/// ```
#[macro_export]
macro_rules! contract {
    ($($contract:ident => $path:literal),* $(,)?) => {
        // Generate sol! definitions
        $(
            $crate::sol! {
                #[sol(rpc, all_derives)]
                $contract,
                $path
            }
        )*

        // Register error parsers
        $(
            $crate::register_contract_errors!($contract);
        )*
    };
}
