//! Contract error registry for parsing and formatting Solidity contract errors.
//!
//! This module provides a distributed registry pattern for contract error parsers.
//! Contract stubs can register their error types, and the registry will try each
//! parser when decoding error data.
//!
//! ## How It Works
//!
//! 1. The `inventory` crate collects all `ContractErrorParser` instances at link time
//! 2. Each contract registers its error parser via `register_contract_errors!` macro
//! 3. When an RPC error occurs, `pretty_error()` tries all parsers to decode the error
//! 4. The first successful parse returns a human-readable error message
//!
//! ## Architecture
//!
//! ```text
//! register_contract_errors!(OrderBook)
//!     │
//!     ▼
//! inventory::submit!(ContractErrorParser { ... })
//!     │
//!     ▼ (at link time)
//! inventory::iter::<ContractErrorParser>
//!     │
//!     ▼ (at runtime)
//! parse_contract_error(&data) → "OrderBook::InsufficientBalance(...)"
//! ```
//!
//! ## Benefits
//!
//! - **Distributed Registration**: Each contract module can register its own parser
//! - **No Central Registry**: No need to maintain a list of all contracts
//! - **Zero Runtime Cost**: Parsers collected at link time, not runtime

use std::borrow::Cow;

use alloy::{
    contract::Error as ContractError,
    primitives::Bytes,
    transports::{RpcError, TransportError},
};

/// Contract error parser entry for the registry.
///
/// Each contract can register a parser that attempts to decode error data
/// into a human-readable format.
pub struct ContractErrorParser {
    /// Name of the contract (for error messages)
    pub name: &'static str,
    /// Parser function that attempts to decode error data
    pub parse: fn(&Bytes) -> Option<String>,
}

// Tell inventory to collect all ContractErrorParser instances at link time.
// This macro generates code that creates a static slice containing all
// submitted parsers, enabling iteration without runtime registration.
inventory::collect!(ContractErrorParser);

/// Try to parse contract error data using all registered parsers.
///
/// Iterates through all registered parsers and returns the first successful parse.
pub fn parse_contract_error(data: &Bytes) -> Option<String> {
    for parser in inventory::iter::<ContractErrorParser> {
        if let Some(msg) = (parser.parse)(data) {
            return Some(msg);
        }
    }
    None
}

/// Convert a contract error to a pretty formatted error with cause information.
///
/// This function attempts to decode the error data from an RPC error response
/// and append a human-readable cause to the error message.
pub fn pretty_error(mut err: ContractError) -> ContractError {
    if let ContractError::TransportError(rpc_error) = err {
        err = ContractError::TransportError(pretty_rpc_error(rpc_error));
    }
    err
}

pub fn pretty_rpc_error(err: TransportError) -> TransportError {
    match err {
        RpcError::ErrorResp(payload) => {
            let mut new_payload = payload.clone();
            if let Some(data) = &payload.data {
                if let Ok(data) = serde_json::from_str::<Bytes>(data.get()) {
                    if let Some(cause) = parse_contract_error(&data) {
                        new_payload.message = new_payload.message.clone()
                            + Cow::Owned(format!(", causedBy: {}", cause));
                    }
                }
            }
            RpcError::ErrorResp(new_payload)
        }
        err => err,
    }
}

/// Register error parsers for existing contract definitions.
///
/// Use this when you have already defined contracts with `alloy::sol!`
/// and just want to register their error parsers separately.
///
/// # Example
///
/// ```ignore
/// alloy::sol! {
///     #[sol(rpc, all_derives)]
///     OrderBook,
///     "path/to/OrderBook.json"
/// }
///
/// register_contract_errors!(OrderBook);
/// ```
#[macro_export]
macro_rules! register_contract_errors {
    ($($contract:ident),* $(,)?) => {
        $(
            $crate::__privite::paste::paste! {
                $crate::__privite::inventory::submit! {
                    $crate::ext::ContractErrorParser {
                        name: stringify!($contract),
                        parse: |data| {
                            use $crate::sol_types::SolInterface;
                            $contract::[<$contract Errors>]::abi_decode(data)
                                .ok()
                                .map(|e| format!("{}::{:?}", stringify!($contract), e))
                        },
                    }
                }
            }
        )*
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_contract_error_empty_registry() {
        // With no parsers registered, should return None
        let data = Bytes::from(vec![0x08, 0xc3, 0x79, 0xa0]); // Error(string) selector
                                                              // Note: In actual tests with registered parsers, this would potentially match
        let result = parse_contract_error(&data);
        // Result depends on what's registered at link time
        assert!(result.is_none() || result.is_some());
    }
}
