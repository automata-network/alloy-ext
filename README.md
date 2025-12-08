# alloy-ext

A production-grade extension library for [Alloy](https://github.com/alloy-rs/alloy) that provides advanced transaction management, nonce lifecycle tracking, and automatic error recovery for Ethereum applications.

## Features

- **Stateful Nonce Management**: Track nonce lifecycle (Reserved → Pending → Confirmed/Abandoned) with automatic gap filling
- **Auto Recovery**: Automatic retry and recovery for nonce errors, network errors, and timeouts
- **Transaction Rebroadcasting**: Periodic rebroadcast to prevent mempool eviction
- **Contract Error Parsing**: Distributed registry for parsing Solidity contract errors into human-readable messages
- **RPC Error Classification**: Intelligent error classification for recovery decisions

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
alloy = { version = "1.1.3", package = "alloy-ext" }
```

## Quick Start

```rust
use alloy::{ext::*, sol};
use std::time::Duration;

// Create provider with HTTP transport
let provider = NetworkProvider::with_http(
    "https://eth-mainnet.g.alchemy.com/v2/YOUR_KEY",
    Some(Duration::from_millis(500)),  // polling interval
    Some(Duration::from_secs(60)),      // receipt timeout
).await?;

// Add signer for transaction signing
let signer = "0x...".parse()?;
let provider = provider.with_signer(signer);

// Send transaction with automatic nonce management
let tx = TransactionRequest::default()
    .to(recipient)
    .value(U256::from(1_000_000_000_000_000_000u128));

let mut tracked = provider.send_transaction_ex(tx).await?;

// Wait for receipt (nonce automatically confirmed on success)
let receipt = tracked.get_receipt().await?;
println!("Transaction mined: {:?}", receipt.transaction_hash());
```

## Nonce Lifecycle

The `StatefulNonceManager` tracks nonces through their complete lifecycle:

```
                       send success
  get_next_nonce() ─────────► mark_sent() ────► confirm()
       │                                  │                      │
       ▼                                  ▼                      ▼
   Reserved ─────────────► Pending ──────► Cleared
       │                                  │
       │ send failure                     │ dropped without confirm
       ▼                                  ▼
   release() ◄──────────── Abandoned
       │                                  │
       ▼                                  ▼
   Released                         Needs gap filling
  (reusable)                       (send cancel tx)
```

### Automatic Recovery

When `auto_recovery` is enabled (default):

- **Nonce too low**: Syncs nonce from chain and retries
- **Nonce too high**: Fills gaps with cancel transactions
- **Network errors**: Retries with exponential backoff
- **Timeouts**: Checks chain state before marking as abandoned

## Configuration

### Provider Configuration

```rust
let provider = provider.with_config(
    ProviderConfig::default()
        .with_auto_recovery(true)         // Enable automatic recovery
        .with_gas_multiplier(1.2)         // Gas multiplier for cancel txs
        .with_max_retries(5)              // Max retry attempts
);
```

### Rebroadcast Configuration

```rust
use std::time::Duration;

let provider = provider.with_rebroadcast(
    RebroadcastConfig::default()
        .with_enabled(true)
        .with_interval(Duration::from_secs(5))
);
```

## Contract Definition and Error Parsing

Use the `contract!` macro to define contracts and automatically register error parsers:

```rust
use alloy::contract;

contract! {
    OrderBook => "out/OrderBook.sol/OrderBook.json",
    Test => "out/Test.sol/Test.json",
}

// Errors from these contracts will be automatically parsed
// into human-readable format
```

Or register error parsers for existing contract definitions:

```rust
use alloy::{sol, register_contract_errors};

sol! {
    #[sol(rpc, all_derives)]
    OrderBook,
    "path/to/OrderBook.json"
}

register_contract_errors!(OrderBook);
```

## TrackedPendingTx

`TrackedPendingTx` wraps a pending transaction with nonce tracking:

```rust
let mut tracked = provider.send_transaction_ex(tx).await?;

// Get transaction info
println!("Hash: {:?}", tracked.tx_hash());
println!("Nonce: {}", tracked.nonce());
println!("From: {:?}", tracked.address());

// Wait for receipt (confirms nonce automatically)
let receipt = tracked.get_receipt().await?;

// Or drop without waiting (marks nonce as abandoned)
drop(tracked);  // Will be recovered on next send
```

## Event Accumulation

Use `PendingTxAccum` to accumulate events from transaction logs:

```rust
use alloy::ext::PendingTxAccum;

let tracked = provider.send_transaction_ex(tx).await?;
let mut accum = PendingTxAccum::with_initial(
    tracked,
    Vec::new(),
    |event: MyContractEvents, results| {
        match event {
            MyContractEvents::Transfer(transfer) => {
                results.push(transfer);
            }
            _ => {}
        }
    }
);

let transfers = accum.result().await?;
```

## Manual Recovery

Recover abandoned nonces manually:

```rust
// Check nonce status
if let Some(status) = provider.nonce_manager().get_status(address).await {
    println!("Pending: {:?}", status.pending_nonces);
    println!("Abandoned: {:?}", status.abandoned_nonces);
}

// Manual recovery
let result = provider.recover(address).await?;
println!("Recovered: {}, Failed: {}", result.recovered_count, result.failed_count);

// With custom options
let result = provider.recover_with_options(
    address,
    RecoveryOptions::default()
        .with_gas_multiplier(1.5)
        .with_max_nonces(20)
        .with_continue_on_failure(true)
).await?;
```

## RPC Error Classification

The library classifies RPC errors for intelligent recovery:

```rust
use alloy::ext::{classify_rpc_error, RpcErrorKind};

match classify_rpc_error(&error) {
    RpcErrorKind::NonceTooLow => { /* sync and retry */ }
    RpcErrorKind::NonceTooHigh => { /* fill gaps */ }
    RpcErrorKind::NetworkError => { /* retry with backoff */ }
    RpcErrorKind::InsufficientFunds => { /* unrecoverable */ }
    // ...
}
```

## Feature Flags

This crate re-exports all Alloy feature flags. Common ones:

```toml
[dependencies]
alloy = { version = "1.1.3", features = ["full"], package = "alloy-ext" }
```

See `Cargo.toml` for the complete list of available features.

## License

Apache