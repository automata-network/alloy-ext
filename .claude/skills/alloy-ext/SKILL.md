---
name: alloy-ext
description: Use when writing Rust code that interacts with Ethereum/EVM blockchains using alloy-ext. Covers contract definitions, NetworkProvider, transaction sending, nonce management, event accumulation, error recovery, and the recommended pattern of wrapping contracts with a typed SDK layer.
user-invocable: false
---

# alloy-ext — Production Ethereum Transaction Management

`alloy-ext` is a Rust crate that extends the [alloy](https://github.com/alloy-rs/alloy) ecosystem with production-grade transaction management: stateful nonce lifecycle, automatic error recovery, transaction rebroadcasting, cancel fallback, and a distributed contract error parsing registry.

**Full alloy compatibility**: `alloy-ext` re-exports the **entire** `alloy` crate via `pub use alloy::*`. This means `alloy-ext` is a **superset** of `alloy` — every type, trait, module, and function from `alloy` is available through `alloy-ext` unchanged. You do NOT need to add `alloy` as a separate dependency. Anything you can do with `alloy` you can do identically with `alloy-ext`:

- `alloy::primitives::{Address, U256, B256, Bytes, ...}`
- `alloy::providers::{Provider, ProviderBuilder, ...}`
- `alloy::signers::local::PrivateKeySigner`
- `alloy::sol!`, `alloy::sol_types::*`
- `alloy::rpc::types::{TransactionRequest, ...}`
- `alloy::network::{Ethereum, EthereumWallet, ...}`
- `alloy::consensus::*`, `alloy::contract::*`, etc.

The only addition is `alloy::ext::*` which contains the extended features (NetworkProvider, TrackedPendingTx, PendingTxAccum, etc.) and the `alloy::contract!` / `alloy::register_contract_errors!` macros.

**Crate import**: In `Cargo.toml`, use the `package` alias so you can write `alloy::` everywhere:

```toml
[dependencies]
alloy = { version = "1.7.4", package = "alloy-ext" }
```

> Always use the latest published version. The `package = "alloy-ext"` alias means `use alloy::*` in code gives you both standard alloy and the `ext::*` extensions. There is no need to depend on `alloy` separately — `alloy-ext` already includes everything.

---

## 1. Defining Contracts — `contract!` Macro

### Finding the ABI JSON files

The `contract!` macro needs the Forge/Foundry output JSON for each contract. Here's how to locate them:

1. **Find the Forge project root**: Look for `foundry.toml` or a `contracts/` / `src/` directory containing `.sol` files.
2. **Find the output directory**: Forge compiles to `out/` by default (configurable via `out` in `foundry.toml`). Run `forge build` if `out/` doesn't exist.
3. **Locate the ABI JSON**: Each contract produces `out/<FileName>.sol/<ContractName>.json`. For example, `contracts/OrderBook.sol` containing `contract OrderBook` → `out/OrderBook.sol/OrderBook.json`.
4. **Path in `contract!`**: Use a relative path from your Rust crate root to the JSON file.

Common directory layouts:

```
# Vendored contracts (recommended for SDK crates)
my-sdk/
├── vendor/my-protocol/out/
│   ├── OrderBook.sol/OrderBook.json      ← use "vendor/my-protocol/out/OrderBook.sol/OrderBook.json"
│   ├── MarginAccount.sol/MarginAccount.json
│   └── ERC20.sol/ERC20.json
├── src/
│   └── stubs.rs

# Or: contract artifacts copied to a flat directory
my-sdk/
├── contract_artifacts/
│   ├── OrderBook.sol/OrderBook.json      ← use "./contract_artifacts/OrderBook.sol/OrderBook.json"
│   └── ERC20.sol/ERC20.json
├── src/
│   └── stubs.rs
```

> **Tip**: When the user mentions a Forge project, search for `foundry.toml` to find the root and `out/` for compiled artifacts. Each `.json` file under `out/` contains `abi`, `bytecode`, `methodIdentifiers`, etc.

### The `contract!` macro

The `contract!` macro wraps `alloy::sol!` and auto-registers error parsers for each contract.

```rust
// src/stubs.rs — define all your contract stubs in one place
alloy::contract! {
    OrderBook => "vendor/out/OrderBook.sol/OrderBook.json",
    MarginAccount => "vendor/out/MarginAccount.sol/MarginAccount.json",
    KuruERC20 => "vendor/out/ERC20.sol/ERC20.json",
}
```

### What code gets generated

For each contract (e.g. `OrderBook`), the macro generates:

| Generated item | Description |
|---|---|
| `OrderBook` module | Contains all function call structs, one per ABI function |
| `OrderBook::OrderBookInstance<P>` | Contract instance bound to an address + provider |
| `OrderBook::OrderBookEvents` | Enum of all events (`Trade`, `OrderCreated`, …) |
| `OrderBook::OrderBookErrors` | Enum of all custom errors |
| `OrderBook::OrderBookCalls` | Enum of all function calls |
| `OrderBook::new(address, provider)` | Constructor → `OrderBookInstance<P>` |

Once you have an instance, every Solidity function becomes a method:

```rust
let ob = OrderBook::new(market_address, provider.clone());

// Read-only calls — returns decoded return value
let tob = ob.bestBidAsk().call_ex().await?;
let order = ob.s_orders(order_id).call_ex().await?;

// State-changing calls — returns TrackedPendingTx
let pending = ob.addBuyOrder(price, size, post_only).send_ex().await?;

// Attach native ETH value
let pending = margin.deposit(user, token, amount).value(amount).send_ex().await?;
```

### Always use `contract!`, not `sol!` directly

**Do NOT** use `alloy::sol! { #[sol(rpc, all_derives)] MyContract, "path/to/ABI.json" }` to define contract stubs. Always use `alloy::contract!` instead — it wraps `sol!` with the correct attributes AND automatically registers error parsers. Using `sol!` directly means you lose automatic contract error decoding and must remember the right attribute combination yourself.

If you encounter legacy code that used `sol!` directly, you can retrofit error registration without changing the `sol!` call:

```rust
// Legacy code — already exists, don't touch
alloy::sol! {
    #[sol(rpc, all_derives)]
    MyContract,
    "path/to/ABI.json"
}
// Add this to get error parsing support:
alloy::register_contract_errors!(MyContract);
```

But for new code, always prefer `alloy::contract!`.

### Handling duplicate structs across contracts

When multiple contracts define the same struct (e.g. both `OrderBook` and `MarginAccount` have a `PublicIdentity` struct with identical fields), the macro generates separate Rust types for each: `OrderBook::PublicIdentity` and `MarginAccount::PublicIdentity`. These are incompatible even though structurally identical.

**Solution**: Define a single canonical Rust struct and implement `From`/`Into` for each generated type using `unsafe { std::mem::transmute(data) }`. Since the structs are generated from the same Solidity definition, their memory layout is identical — `transmute` is safe here and also serves as a compile-time guarantee: if the structs ever diverge in layout, the transmute will fail to compile (size mismatch).

```rust
// src/stubs.rs
alloy::contract! {
    ContractA => "out/ContractA.sol/ContractA.json",
    ContractB => "out/ContractB.sol/ContractB.json",
}

// Shared struct that appears in both ContractA and ContractB ABIs.
// Define it once as the canonical type used in business logic.
alloy::sol! {
    struct SharedConfig {
        uint256 param1;
        address param2;
    }
}

// transmute is safe because the structs have identical Solidity definitions
// and therefore identical memory layouts. If they ever differ, this won't compile.
impl From<SharedConfig> for ContractA::SharedConfig {
    fn from(data: SharedConfig) -> Self {
        unsafe { std::mem::transmute(data) }
    }
}

impl From<SharedConfig> for ContractB::SharedConfig {
    fn from(data: SharedConfig) -> Self {
        unsafe { std::mem::transmute(data) }
    }
}

// Also works in reverse — convert from generated type back to canonical
impl From<ContractA::SharedConfig> for SharedConfig {
    fn from(data: ContractA::SharedConfig) -> Self {
        unsafe { std::mem::transmute(data) }
    }
}

// You can also re-export one contract's type as the canonical type:
pub type SomeType = ContractA::SomeType;
```

This keeps the business logic working with a single type while the contract layer handles conversions. The `transmute` approach is preferred over field-by-field conversion because:
- It's zero-cost (no field copying)
- It acts as a compile-time assertion that the structs are layout-compatible
- It scales to complex nested structs without manual field mapping

---

## 2. NetworkProvider — Creation and Configuration

`NetworkProvider` is an enum with two variants:
- `Http` — read-only, no signer
- `Wallet` — full signing + nonce management

### Filler stack (applied automatically)

```
ChainIdFiller → BoostGasFiller → BlobGasFiller → NonceFiller<StatefulNonceManager> → WalletFiller
```

### Creating a provider

```rust
use alloy::ext::{NetworkProvider, ProviderEx};
use alloy::providers::Provider;
use alloy::signers::local::PrivateKeySigner;
use std::time::Duration;

// Step 1: Create HTTP provider (read-only)
let provider = NetworkProvider::with_http(
    "https://rpc.example.com",       // RPC URL
    Some(Duration::from_millis(500)), // polling interval (None = default)
    Some(Duration::from_secs(30)),    // receipt timeout (None = no timeout)
    100,                              // gas boost multiplier (100 = no boost, 110 = 10% boost)
).await?;

// Step 2: Add signer for write operations
let signer: PrivateKeySigner = "0xprivate_key".parse()?;
let provider = provider.with_signer(signer);

// Step 3: Configure behavior (all optional, all have sensible defaults)
let provider = provider
    .with_rebroadcast_interval(Duration::from_secs(5))  // rebroadcast pending TXs
    .with_receipt_timeout(Duration::from_secs(60))
    .with_config(ProviderConfig::default()
        .with_auto_recovery(true)      // auto-recover nonce errors (default: true)
        .with_max_retries(3)           // max send retries (default: 3)
        .with_gas_multiplier(1.1)      // recovery gas multiplier (default: 1.1)
        .with_rebroadcast(RebroadcastConfig::default().with_interval(Duration::from_secs(5)))
        .with_cancel(CancelConfig::default().with_gas_multiplier(2.0)));
```

### Key provider methods

| Method | Description |
|---|---|
| `provider.from()? → Address` | Get signer address (errors if Http variant) |
| `provider.get_chain_id().await?` | Query chain ID from RPC |
| `provider.get_balance(addr).await?` | Standard alloy Provider method |
| `provider.get_transaction_count(addr).await?` | Get on-chain nonce |
| `provider.send_transaction_ex(tx).await?` | Send TX with nonce tracking + auto recovery |
| `provider.recover(addr).await?` | Manually recover abandoned nonces |
| `provider.fill_nonce_gap(nonce, tx_hash, gas_mult).await?` | Fill a specific nonce gap |
| `provider.nonce_manager()` | Access the `StatefulNonceManager` |

---

## 3. Sending Transactions

### The `send_ex()` / `call_ex()` pattern

These are extension methods from `CallBuilderEx` trait, available on any contract call builder:

```rust
use alloy::ext::CallBuilderEx;

// Read-only call (no gas, no nonce)
let result = contract.someViewFunction(arg1, arg2).call_ex().await?;

// State-changing transaction (allocates nonce, signs, sends)
let mut tracked = contract.someFunction(arg1, arg2).send_ex().await?;
let receipt = tracked.get_receipt().await?;
```

### `call_ex()` vs `call()`
`call_ex()` adds contract error prettification — if the call reverts, the error message includes the decoded Solidity custom error (e.g. `"OrderBook::InsufficientBalance(...)"`).

### `send_ex()` vs `send()`
`send_ex()` returns `TrackedPendingTx` which:
- Tracks nonce lifecycle (RESERVED → PENDING → CONFIRMED/ABANDONED)
- Auto-confirms nonce on `get_receipt()` success
- Auto-marks nonce ABANDONED on `Drop` (prevents nonce leaks)
- Supports rebroadcasting and cancel fallback

### Raw transaction request (without contract)

```rust
use alloy::rpc::types::TransactionRequest;

let tx = TransactionRequest::default()
    .to(recipient)
    .value(alloy::primitives::U256::from(1_000_000_000u64));

let mut tracked = provider.send_transaction_ex(tx).await?;
let receipt = tracked.get_receipt().await?;
```

---

## 4. TrackedPendingTx — Transaction Lifecycle

```
send_transaction_ex() → TrackedPendingTx (nonce: PENDING)
        ├── get_receipt() success  → nonce: CONFIRMED
        ├── Drop without receipt   → nonce: ABANDONED (needs gap filling)
        └── resolution()           → TxResolution enum (full control)
```

### Simple usage

```rust
let mut tracked = provider.send_transaction_ex(tx).await?;
let tx_hash = tracked.tx_hash();         // available immediately
let receipt = tracked.get_receipt().await?;  // waits, confirms nonce
```

### Full resolution control

```rust
let mut tracked = provider.send_transaction_ex(tx).await?;
match tracked.resolution().await? {
    TxResolution::Confirmed { receipt } => {
        // Happy path — original TX mined
    }
    TxResolution::OriginalConfirmedAfterCancel { receipt, cancel_tx_hash } => {
        // Original TX won the race after cancel was sent
    }
    TxResolution::Cancelled { cancel_receipt, original_tx_hash } => {
        // Cancel TX won — original was replaced
    }
    TxResolution::Timeout { original_tx_hash, cancel_tx_hash, nonce } => {
        // Both TXs timed out — manual intervention needed
    }
}
```

### Two-phase flow

1. **Phase 1**: Wait for receipt with periodic rebroadcasting
2. **Phase 1 timeout**: Check chain state (TX might have been mined)
3. **Phase 2** (if cancel enabled): Send cancel TX (0 ETH to self, same nonce, higher gas), race original vs cancel

---

## 5. PendingTxAccum — Event Accumulation

`PendingTxAccum<T, E>` wraps `TrackedPendingTx` and parses events from the receipt logs into a typed result `T`.

```rust
use alloy::ext::PendingTxAccum;

// Define result type
#[derive(Default, Clone)]
struct SwapResult {
    amount_in: U256,
    amount_out: U256,
}

// Send and accumulate
let tracked = provider.send_transaction_ex(swap_tx).await?;
let mut accum = PendingTxAccum::new(tracked, |event: PoolEvents, result: &mut SwapResult| {
    if let PoolEvents::Swap(swap) = event {
        result.amount_in = swap.amount_in;
        result.amount_out = swap.amount_out;
    }
});

let swap_result: SwapResult = accum.result().await?;
```

### `PendingTxAccum::new` vs `PendingTxAccum::with_initial`

- `new(tracked, callback)` — starts with `T::default()`
- `with_initial(tracked, initial_value, callback)` — starts with a custom initial value

### Key methods

| Method | Description |
|---|---|
| `.tx_hash()` | Get original TX hash (available immediately) |
| `.result().await?` | Wait for receipt, parse events, return accumulated `T` |
| `.receipt().await?` | Wait for receipt only (no event parsing) |
| `.resolution().await?` | Full `TxResolution` control |

---

## 6. Nonce Management

The `StatefulNonceManager` tracks nonce lifecycle with atomic state transitions:

```
RESERVED ──► PENDING ──► CONFIRMED
                │
                └──► ABANDONED (needs gap filling)
```

Nonce management is **automatic** — you rarely interact with it directly. Key behaviors:

- `send_transaction_ex()` allocates nonce (RESERVED), sends, marks PENDING
- `get_receipt()` success → marks CONFIRMED, clears slot
- `TrackedPendingTx::Drop` without receipt → marks ABANDONED (lock-free via AtomicU8)
- `send_transaction_ex()` with `auto_recovery: true` proactively fills gaps before sending

### Monitoring nonce state

```rust
if let Some(status) = provider.nonce_manager().get_status(address).await {
    println!("Base nonce: {}", status.base_nonce);
    println!("Next nonce: {}", status.next_nonce);
    println!("Pending: {:?}", status.pending_nonces);
    println!("Abandoned: {:?}", status.abandoned_nonces);
}
```

### Manual recovery

```rust
let result = provider.recover(address).await?;
// result.recovered_count, result.failed_count, result.results
```

---

## 7. Error Handling

### RPC Error Classification

`classify_rpc_error()` maps RPC error strings to `RpcErrorKind`:

| Kind | Recoverable | Auto-recovery action |
|---|---|---|
| `NonceTooLow` | Yes | `sync()` nonce from chain, retry |
| `NonceTooHigh` | Yes | `recover()` abandoned nonces, retry |
| `ReplacementUnderpriced` | Yes | Increase gas, retry |
| `NetworkError` | Yes | Exponential backoff, retry |
| `AlreadyKnown` | Yes | TX in mempool already |
| `IntrinsicGasTooLow` | Yes | Re-estimate gas, retry |
| `InsufficientFunds` | **No** | User must add funds |
| `Unknown` | **No** | — |

### Contract Error Prettification

When a call reverts, `call_ex()` and `send_ex()` automatically decode custom Solidity errors:

```
// Before: "execution reverted: 0x08c379a0..."
// After:  "execution reverted: 0x08c379a0..., causedBy: OrderBook::InsufficientBalance(...)"
```

This works because `contract!` auto-registers error parsers via the `inventory` crate (zero-cost, link-time collection).

---

## 8. Recommended Pattern: Wrapping Contracts with a Typed SDK Layer

**Do NOT use generated contract instances directly in business logic.** Instead, build a domain-specific SDK layer on top. This pattern:

- Hides raw Solidity types behind human-friendly Rust APIs
- Centralizes unit conversion (wei ↔ decimals, price ticks ↔ decimals)
- Defines typed result structs with `PendingTxAccum` aliases
- Makes error context richer with `.with_context()`
- Keeps provider management (signer, read-only) in one place

### Step-by-step pattern

#### Step 1: Define contracts in a `stubs.rs`

```rust
// src/stubs.rs
alloy::contract! {
    MyDex => "out/MyDex.sol/MyDex.json",
    MyToken => "out/ERC20.sol/ERC20.json",
}
```

#### Step 2: Define domain result types + PendingTxAccum aliases

```rust
// src/types.rs
use alloy::ext::PendingTxAccum;
use crate::stubs::MyDex;

#[derive(Default, Clone)]
pub struct SwapResult {
    pub amount_in: U256,
    pub amount_out: U256,
    pub price: Decimal,
}

#[derive(Default, Clone)]
pub struct AddLiquidityResult {
    pub shares: U256,
}

// Type aliases — one per operation, binding result type to event enum
pub type PendingSwapResult = PendingTxAccum<SwapResult, MyDex::MyDexEvents>;
pub type PendingAddLiquidityResult = PendingTxAccum<AddLiquidityResult, MyDex::MyDexEvents>;
```

#### Step 3: Build a wrapper struct

```rust
// src/dex.rs
use alloy::ext::{NetworkProvider, CallBuilderEx, PendingTxAccum};
use alloy::primitives::{Address, U256};
use anyhow::Context;

pub struct DexClient {
    provider: NetworkProvider,
}

impl DexClient {
    pub fn new(provider: NetworkProvider) -> Self {
        Self { provider }
    }

    // --- Read operations (call_ex) ---

    pub async fn get_price(&self, pool: Address) -> anyhow::Result<Decimal> {
        let dex = MyDex::new(pool, self.provider.clone());
        let raw_price = dex.getPrice().call_ex().await?;
        Ok(self.raw_price_to_decimal(raw_price))
    }

    pub async fn get_balance(&self, pool: Address, token: Address) -> anyhow::Result<U256> {
        let dex = MyDex::new(pool, self.provider.clone());
        let balance = dex.getBalance(token).call_ex().await
            .with_context(|| format!("failed to get balance for token {}", token))?;
        Ok(balance)
    }

    // --- Write operations (send_ex → PendingTxAccum) ---

    pub async fn swap(
        &self,
        pool: Address,
        token_in: Address,
        amount_in: U256,
        min_amount_out: U256,
    ) -> anyhow::Result<PendingSwapResult> {
        let dex = MyDex::new(pool, self.provider.clone());

        let pending = dex
            .swap(token_in, amount_in, min_amount_out)
            .send_ex()
            .await
            .with_context(|| format!("swap failed: {} of {}", amount_in, token_in))?;

        Ok(PendingTxAccum::new(pending, |event, result: &mut SwapResult| {
            if let MyDex::MyDexEvents::Swap(swap) = event {
                result.amount_in = swap.amountIn;
                result.amount_out = swap.amountOut;
            }
        }))
    }

    // --- Write with ETH value ---

    pub async fn swap_eth(
        &self,
        pool: Address,
        amount: U256,
        min_out: U256,
    ) -> anyhow::Result<PendingSwapResult> {
        let dex = MyDex::new(pool, self.provider.clone());

        let pending = dex
            .swapETH(min_out)
            .value(amount)  // attach native ETH
            .send_ex()
            .await
            .with_context(|| "ETH swap failed")?;

        Ok(PendingTxAccum::new(pending, |event, result: &mut SwapResult| {
            if let MyDex::MyDexEvents::Swap(swap) = event {
                result.amount_in = swap.amountIn;
                result.amount_out = swap.amountOut;
            }
        }))
    }
}
```

#### Step 4: Top-level SDK with provider management

```rust
// src/sdk.rs
use alloy::ext::NetworkProvider;
use alloy::signers::local::PrivateKeySigner;

pub struct MySdk {
    http_provider: NetworkProvider,
}

impl MySdk {
    pub async fn new(rpc_url: &str) -> anyhow::Result<Self> {
        let http_provider = NetworkProvider::with_http(
            rpc_url,
            Some(Duration::from_millis(500)),
            Some(Duration::from_secs(30)),
            100,
        ).await?
        .with_rebroadcast_interval(Duration::from_secs(10));

        Ok(Self { http_provider })
    }

    /// Read-only client (no signer needed)
    pub fn dex_readonly(&self) -> DexClient {
        DexClient::new(self.http_provider.clone())
    }

    /// Client with signer for write operations
    pub fn dex(&self, signer: PrivateKeySigner) -> DexClient {
        DexClient::new(self.http_provider.with_signer(signer))
    }
}
```

#### Step 5: Usage by the caller

```rust
let sdk = MySdk::new("https://rpc.example.com").await?;

// Read (no signer)
let price = sdk.dex_readonly().get_price(pool).await?;

// Write (with signer)
let dex = sdk.dex(signer);
let mut pending = dex.swap(pool, token_in, amount_in, min_out).await?;
println!("TX sent: {:?}", pending.tx_hash());

let result = pending.result().await?;
println!("Got {} out", result.amount_out);
```

### Key principles

1. **Callers never see raw Solidity types** — expose `Decimal`, domain structs
2. **One wrapper method per contract function** — centralizes conversion + error context
3. **Return `PendingTxAccum<DomainResult, ContractEvents>`** — caller calls `.result().await?`
4. **Provide both read-only and signer variants** via `dex_readonly()` / `dex(signer)`
5. **Use `.with_context()`** on every `.send_ex()` and `.call_ex()` for rich error messages

---

## 9. Quick Reference

### Imports cheat sheet

```rust
use alloy::ext::{
    NetworkProvider,       // Provider enum (Http / Wallet)
    ProviderEx,            // Extension trait (send_transaction_ex, fill, etc.)
    CallBuilderEx,         // Extension trait (send_ex, call_ex)
    TrackedPendingTx,      // Pending TX with nonce tracking
    PendingTxAccum,        // Event accumulator
    TxResolution,          // Confirmed / Cancelled / Timeout
    ProviderConfig,        // Provider configuration
    RebroadcastConfig,     // Rebroadcast settings
    CancelConfig,          // Cancel fallback settings
    RecoveryResult,        // Recovery outcome
    RecoveryOptions,       // Recovery configuration
    StatefulNonceManager,  // Nonce manager
    NonceStatus,           // Nonce state snapshot
    RpcErrorKind,          // Error classification
    classify_rpc_error,    // Error classifier function
};
use alloy::primitives::{Address, U256, B256, U96, Bytes};
use alloy::signers::local::PrivateKeySigner;
use alloy::providers::Provider;
use alloy::sol_types::SolEventInterface;
use alloy::rpc::types::TransactionRequest;
```

### Common flow

```
contract!  →  ContractName::new(addr, provider)
           →  .method().call_ex().await?          (read)
           →  .method().send_ex().await?          (write → TrackedPendingTx)
           →  PendingTxAccum::new(tracked, cb)    (wrap with event handler)
           →  accum.result().await?               (wait + parse events)
```
