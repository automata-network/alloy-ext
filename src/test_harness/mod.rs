//! Anvil-based test harness for simulating various exception scenarios.
//!
//! This module provides `AnvilTestHarness` for comprehensive testing of
//! blockchain interactions, particularly around nonce management, gas handling,
//! transaction failures, and network exceptions.
//!
//! # Example
//!
//! ```ignore
//! use kuru_sdk::alloy_utils::test_harness::AnvilTestHarness;
//!
//! #[tokio::test]
//! async fn test_nonce_too_low() {
//!     let harness = AnvilTestHarness::new().await.unwrap();
//!
//!     // Simulate nonce too low error
//!     let result = harness.simulate_nonce_too_low().await;
//!     assert!(result.is_err());
//! }
//! ```

#[cfg(test)]
mod error_scenarios;
mod scenario;

pub use scenario::*;

use std::time::Duration;

use crate::ext::NetworkProvider;
use alloy::{
    network::{Ethereum, EthereumWallet, TransactionBuilder},
    node_bindings::{Anvil, AnvilInstance},
    primitives::{Address, Bytes, B256, U256},
    providers::{ext::AnvilApi, Provider, ProviderBuilder, RootProvider},
    rpc::types::TransactionRequest,
    signers::local::PrivateKeySigner,
};
use anyhow::{anyhow, Result};

// ============================================================================
// Snapshot State
// ============================================================================

/// Represents a snapshot of the blockchain state for rollback
#[derive(Debug, Clone, Copy)]
pub struct SnapshotId(pub U256);

// ============================================================================
// AnvilTestHarness
// ============================================================================

/// Test harness for simulating various exception scenarios using Anvil.
///
/// This harness provides methods to:
/// - Spawn and manage local Anvil nodes
/// - Simulate nonce-related exceptions
/// - Simulate gas and transaction failures
/// - Control mining behavior
/// - Manipulate account state (balance, nonce, storage)
/// - Create and restore snapshots
pub struct AnvilTestHarness {
    /// The Anvil instance
    instance: AnvilInstance,
    /// The provider connected to Anvil
    provider: NetworkProvider,
    /// Pre-funded test accounts from Anvil
    accounts: Vec<Address>,
    /// Private keys for test accounts
    keys: Vec<PrivateKeySigner>,
    /// Chain ID
    chain_id: u64,
}

impl AnvilTestHarness {
    /// Create a new test harness with a fresh Anvil instance
    pub async fn new() -> Result<Self> {
        Self::with_config(|anvil| anvil).await
    }

    /// Create a new test harness with custom Anvil configuration
    pub async fn with_config<F>(config: F) -> Result<Self>
    where
        F: FnOnce(Anvil) -> Anvil,
    {
        let instance = config(Anvil::new()).try_spawn()?;
        let endpoint_url: String = instance.endpoint().parse()?;
        let provider =
            NetworkProvider::with_http(&endpoint_url, None, Some(Duration::from_secs(5)), 100).await?;

        let accounts = instance.addresses().to_vec();
        let keys: Vec<PrivateKeySigner> =
            instance.keys().iter().map(|k| k.clone().into()).collect();
        let chain_id = provider.get_chain_id().await?;

        Ok(Self {
            instance,
            provider,
            accounts,
            keys,
            chain_id,
        })
    }

    pub async fn new_provider(&self, signer: Option<Address>) -> Result<NetworkProvider> {
        let endpoint_url: String = self.instance.endpoint().parse()?;
        let provider =
            NetworkProvider::with_http(&endpoint_url, None, Some(Duration::from_secs(5)), 100).await?;
        if let Some(signer_addr) = signer {
            let key = self
                .keys
                .iter()
                .find(|k| k.address() == signer_addr)
                .ok_or_else(|| anyhow!("Signer address not found in test accounts"))?;
            Ok(provider.with_signer(key.clone()))
        } else {
            Ok(provider)
        }
    }

    /// Create a harness that forks from a remote RPC endpoint
    pub async fn fork(rpc_url: &str) -> Result<Self> {
        Self::with_config(|anvil| anvil.fork(rpc_url)).await
    }

    /// Create a harness with disabled auto-mining (manual mining control)
    pub async fn with_manual_mining() -> Result<Self> {
        Self::with_config(|anvil| anvil.arg("--no-mining")).await
    }

    /// Get the RPC endpoint URL
    pub fn endpoint(&self) -> String {
        self.instance.endpoint()
    }

    /// Get the provider
    pub fn provider(&self) -> &RootProvider<Ethereum> {
        self.provider.root()
    }

    /// Get pre-funded test accounts
    pub fn accounts(&self) -> &[Address] {
        &self.accounts
    }

    /// Get the first test account (Alice)
    pub fn alice(&self) -> Address {
        self.accounts[0]
    }

    /// Get the second test account (Bob)
    pub fn bob(&self) -> Address {
        self.accounts[1]
    }

    /// Get the signer for a specific account index
    pub fn signer(&self, index: usize) -> &PrivateKeySigner {
        &self.keys[index]
    }

    /// Get the wallet for a specific account index
    pub fn wallet(&self, index: usize) -> EthereumWallet {
        EthereumWallet::new(self.keys[index].clone())
    }

    /// Get the chain ID
    pub fn chain_id(&self) -> u64 {
        self.chain_id
    }

    /// Get a NetworkProvider with signer capability for a specific account.
    ///
    /// This is useful for testing with `send_transaction_ex()` and `PendingTxAccum`.
    pub fn network_provider_with_signer(&self, account_index: usize) -> NetworkProvider {
        self.provider.with_signer(self.keys[account_index].clone())
    }

    pub fn alice_provider(&self) -> NetworkProvider {
        self.network_provider_with_signer(0)
    }

    pub fn bob_provider(&self) -> NetworkProvider {
        self.network_provider_with_signer(1)
    }

    /// Get a NetworkProvider with signer capability and custom receipt timeout.
    ///
    /// This is useful for testing timeout scenarios.
    pub fn network_provider_with_signer_and_timeout(
        &self,
        account_index: usize,
        timeout: Duration,
    ) -> NetworkProvider {
        self.provider
            .with_signer(self.keys[account_index].clone())
            .with_receipt_timeout(timeout)
    }

    /// Get the internal NetworkProvider (without signer)
    pub fn network_provider(&self) -> &NetworkProvider {
        &self.provider
    }

    // ========================================================================
    // Snapshot Management
    // ========================================================================

    /// Create a snapshot of the current blockchain state
    pub async fn snapshot(&self) -> Result<SnapshotId> {
        let id = self.provider.anvil_snapshot().await?;
        Ok(SnapshotId(id))
    }

    /// Revert to a previously created snapshot
    pub async fn revert(&self, snapshot: SnapshotId) -> Result<bool> {
        let reverted = self.provider.anvil_revert(snapshot.0).await?;
        Ok(reverted)
    }

    // ========================================================================
    // Account State Manipulation
    // ========================================================================

    /// Set the ETH balance for an account
    pub async fn set_balance(&self, address: Address, balance: U256) -> Result<()> {
        self.provider.anvil_set_balance(address, balance).await?;
        Ok(())
    }

    /// Set the nonce for an account
    pub async fn set_nonce(&self, address: Address, nonce: u64) -> Result<()> {
        self.provider.anvil_set_nonce(address, nonce).await?;
        Ok(())
    }

    /// Set contract code at an address
    pub async fn set_code(&self, address: Address, code: Bytes) -> Result<()> {
        self.provider.anvil_set_code(address, code).await?;
        Ok(())
    }

    /// Set storage at a specific slot for an address
    pub async fn set_storage(&self, address: Address, slot: U256, value: U256) -> Result<()> {
        self.provider
            .anvil_set_storage_at(address, slot, value.into())
            .await?;
        Ok(())
    }

    /// Get the current nonce for an address
    pub async fn get_nonce(&self, address: Address) -> Result<u64> {
        let nonce = self.provider.get_transaction_count(address).await?;
        Ok(nonce)
    }

    /// Get the current balance for an address
    pub async fn get_balance(&self, address: Address) -> Result<U256> {
        let balance = self.provider.get_balance(address).await?;
        Ok(balance)
    }

    // ========================================================================
    // Mining Control
    // ========================================================================

    /// Mine a single block
    pub async fn mine_block(&self) -> Result<()> {
        self.provider.anvil_mine(Some(1), None).await?;
        Ok(())
    }

    /// Mine multiple blocks
    pub async fn mine_blocks(&self, count: u64) -> Result<()> {
        self.provider.anvil_mine(Some(count), None).await?;
        Ok(())
    }

    /// Mine blocks with a specific time interval between them
    pub async fn mine_blocks_with_interval(&self, count: u64, interval_secs: u64) -> Result<()> {
        self.provider
            .anvil_mine(Some(count), Some(interval_secs))
            .await?;
        Ok(())
    }

    /// Enable auto-mining (mine a block for each transaction)
    pub async fn enable_automine(&self) -> Result<()> {
        self.provider.anvil_set_auto_mine(true).await?;
        Ok(())
    }

    /// Disable auto-mining (manual mining mode)
    pub async fn disable_automine(&self) -> Result<()> {
        self.provider.anvil_set_auto_mine(false).await?;
        Ok(())
    }

    /// Set the block time interval for auto-mining
    pub async fn set_block_interval(&self, interval_secs: u64) -> Result<()> {
        self.provider
            .anvil_set_interval_mining(interval_secs)
            .await?;
        Ok(())
    }

    /// Advance time by a specific duration
    pub async fn advance_time(&self, duration: Duration) -> Result<()> {
        self.provider
            .anvil_increase_time(duration.as_secs())
            .await?;
        Ok(())
    }

    /// Set the next block's timestamp
    pub async fn set_next_block_timestamp(&self, timestamp: u64) -> Result<()> {
        self.provider
            .anvil_set_next_block_timestamp(timestamp)
            .await?;
        Ok(())
    }

    // ========================================================================
    // Transaction Control
    // ========================================================================

    /// Drop a transaction from the mempool
    pub async fn drop_transaction(&self, tx_hash: B256) -> Result<Option<B256>> {
        let dropped = self.provider.anvil_drop_transaction(tx_hash).await?;
        Ok(dropped)
    }

    /// Enable impersonation for an address (send tx without private key)
    pub async fn impersonate(&self, address: Address) -> Result<()> {
        self.provider.anvil_impersonate_account(address).await?;
        Ok(())
    }

    /// Stop impersonating an address
    pub async fn stop_impersonating(&self, address: Address) -> Result<()> {
        self.provider
            .anvil_stop_impersonating_account(address)
            .await?;
        Ok(())
    }

    /// Enable auto-impersonation (no signature required for any tx)
    pub async fn enable_auto_impersonate(&self) -> Result<()> {
        self.provider.anvil_auto_impersonate_account(true).await?;
        Ok(())
    }

    /// Disable auto-impersonation
    pub async fn disable_auto_impersonate(&self) -> Result<()> {
        self.provider.anvil_auto_impersonate_account(false).await?;
        Ok(())
    }

    // ========================================================================
    // Helper: Get endpoint URL
    // ========================================================================

    fn endpoint_url(&self) -> reqwest::Url {
        self.instance.endpoint().parse().unwrap()
    }

    // ========================================================================
    // Exception Simulation - Nonce Related
    // ========================================================================

    /// Simulate a "nonce too low" error.
    ///
    /// This sends a transaction with a nonce that has already been used.
    pub async fn simulate_nonce_too_low(&self) -> Result<TransactionSimulationResult> {
        let from = self.alice();
        let to = self.bob();

        // First, send a normal transaction to use nonce 0
        let wallet = self.wallet(0);
        let provider = ProviderBuilder::new()
            .wallet(wallet.clone())
            .connect_http(self.endpoint_url());

        let tx = TransactionRequest::default()
            .with_from(from)
            .with_to(to)
            .with_value(U256::from(1000))
            .with_nonce(0)
            .with_chain_id(self.chain_id)
            .with_gas_limit(21000)
            .with_max_fee_per_gas(20_000_000_000u128)
            .with_max_priority_fee_per_gas(1_000_000_000u128);

        provider.send_transaction(tx.clone()).await?.watch().await?;

        // Now try to send another transaction with the same nonce (0)
        let result = provider.send_transaction(tx).await;

        match result {
            Ok(_) => Ok(TransactionSimulationResult::UnexpectedSuccess),
            Err(e) => Ok(TransactionSimulationResult::ExpectedError(e.to_string())),
        }
    }

    /// Simulate a nonce gap scenario.
    ///
    /// This sends a transaction with a nonce that skips one or more values.
    pub async fn simulate_nonce_gap(&self, gap_size: u64) -> Result<TransactionSimulationResult> {
        let from = self.alice();
        let to = self.bob();
        let current_nonce = self.get_nonce(from).await?;

        let wallet = self.wallet(0);
        let provider = ProviderBuilder::new()
            .wallet(wallet)
            .connect_http(self.endpoint_url());

        // Try to send with a nonce that creates a gap
        let tx = TransactionRequest::default()
            .with_from(from)
            .with_to(to)
            .with_value(U256::from(1000))
            .with_nonce(current_nonce + gap_size)
            .with_chain_id(self.chain_id)
            .with_gas_limit(21000)
            .with_max_fee_per_gas(20_000_000_000u128)
            .with_max_priority_fee_per_gas(1_000_000_000u128);

        // Disable automine to see the tx stuck in mempool
        self.disable_automine().await?;

        let result = provider.send_transaction(tx).await;

        // Re-enable automine
        self.enable_automine().await?;

        match result {
            Ok(pending) => Ok(TransactionSimulationResult::Pending {
                tx_hash: *pending.tx_hash(),
                description: format!(
                    "Transaction with nonce {} submitted (gap of {}). \
                     Will not be mined until nonces {} to {} are filled.",
                    current_nonce + gap_size,
                    gap_size,
                    current_nonce,
                    current_nonce + gap_size - 1
                ),
            }),
            Err(e) => Ok(TransactionSimulationResult::ExpectedError(e.to_string())),
        }
    }

    /// Simulate an "insufficient funds" error.
    ///
    /// This sends a transaction where the sender doesn't have enough ETH.
    pub async fn simulate_insufficient_funds(&self) -> Result<TransactionSimulationResult> {
        let from = self.alice();
        let to = self.bob();

        // Get current balance and try to send more
        let balance = self.get_balance(from).await?;

        let wallet = self.wallet(0);
        let provider = ProviderBuilder::new()
            .wallet(wallet)
            .connect_http(self.endpoint_url());

        // Try to send more than we have
        let tx = TransactionRequest::default()
            .with_from(from)
            .with_to(to)
            .with_value(balance + U256::from(1)) // More than balance
            .with_chain_id(self.chain_id)
            .with_gas_limit(21000)
            .with_max_fee_per_gas(20_000_000_000u128)
            .with_max_priority_fee_per_gas(1_000_000_000u128);

        let result = provider.send_transaction(tx).await;

        match result {
            Ok(_) => Ok(TransactionSimulationResult::UnexpectedSuccess),
            Err(e) => Ok(TransactionSimulationResult::ExpectedError(e.to_string())),
        }
    }

    // ========================================================================
    // Exception Simulation - Transaction Failures
    // ========================================================================

    /// Deploy a contract that will revert on call
    pub async fn deploy_reverting_contract(&self) -> Result<Address> {
        let from = self.alice();

        // Contract that always reverts when called.
        // Init code (12 bytes): copies runtime code to memory and returns it
        //   PUSH1 0x05  (runtime size)
        //   PUSH1 0x0c  (runtime offset in code)
        //   PUSH1 0x00  (memory destination)
        //   CODECOPY
        //   PUSH1 0x05  (runtime size)
        //   PUSH1 0x00  (memory offset)
        //   RETURN
        // Runtime code (5 bytes): always reverts
        //   PUSH1 0x00 PUSH1 0x00 REVERT
        let bytecode = Bytes::from(vec![
            0x60, 0x05, // PUSH1 5
            0x60, 0x0c, // PUSH1 12
            0x60, 0x00, // PUSH1 0
            0x39, // CODECOPY
            0x60, 0x05, // PUSH1 5
            0x60, 0x00, // PUSH1 0
            0xf3, // RETURN
            // Runtime code starts here (offset 12)
            0x60, 0x00, // PUSH1 0
            0x60, 0x00, // PUSH1 0
            0xfd, // REVERT
        ]);

        let wallet = self.wallet(0);
        let provider = ProviderBuilder::new()
            .wallet(wallet)
            .connect_http(self.endpoint_url());

        let tx = TransactionRequest::default()
            .with_from(from)
            .with_chain_id(self.chain_id)
            .with_gas_limit(100000)
            .with_max_fee_per_gas(20_000_000_000u128)
            .with_max_priority_fee_per_gas(1_000_000_000u128)
            .with_deploy_code(bytecode);

        let pending = provider.send_transaction(tx).await?;
        let receipt = pending.get_receipt().await?;

        receipt
            .contract_address
            .ok_or_else(|| anyhow!("Contract deployment failed"))
    }

    /// Simulate a transaction revert.
    ///
    /// This calls a contract that always reverts.
    pub async fn simulate_revert(&self) -> Result<TransactionSimulationResult> {
        let reverting_contract = self.deploy_reverting_contract().await?;
        let from = self.alice();

        let wallet = self.wallet(0);
        let provider = ProviderBuilder::new()
            .wallet(wallet)
            .connect_http(self.endpoint_url());

        let tx = TransactionRequest::default()
            .with_from(from)
            .with_to(reverting_contract)
            .with_chain_id(self.chain_id)
            .with_gas_limit(100000)
            .with_max_fee_per_gas(20_000_000_000u128)
            .with_max_priority_fee_per_gas(1_000_000_000u128);

        let result = provider.send_transaction(tx).await;

        match result {
            Ok(pending) => {
                // Transaction was sent, check if it reverted
                let receipt = pending.get_receipt().await?;
                if receipt.status() {
                    Ok(TransactionSimulationResult::UnexpectedSuccess)
                } else {
                    Ok(TransactionSimulationResult::Reverted {
                        tx_hash: receipt.transaction_hash,
                        gas_used: receipt.gas_used,
                    })
                }
            }
            Err(e) => Ok(TransactionSimulationResult::ExpectedError(e.to_string())),
        }
    }

    /// Simulate a dropped transaction (transaction removed from mempool)
    pub async fn simulate_dropped_transaction(&self) -> Result<TransactionSimulationResult> {
        let from = self.alice();
        let to = self.bob();

        let wallet = self.wallet(0);
        let provider = ProviderBuilder::new()
            .wallet(wallet)
            .connect_http(self.endpoint_url());

        // Disable automine
        self.disable_automine().await?;

        let tx = TransactionRequest::default()
            .with_from(from)
            .with_to(to)
            .with_value(U256::from(1000))
            .with_chain_id(self.chain_id)
            .with_gas_limit(21000)
            .with_max_fee_per_gas(20_000_000_000u128)
            .with_max_priority_fee_per_gas(1_000_000_000u128);

        let pending = provider.send_transaction(tx).await?;
        let tx_hash = *pending.tx_hash();

        // Drop the transaction from mempool
        let dropped = self.drop_transaction(tx_hash).await?;

        // Re-enable automine
        self.enable_automine().await?;

        Ok(TransactionSimulationResult::Dropped {
            tx_hash,
            was_dropped: dropped.is_some(),
        })
    }

    // ========================================================================
    // Helpers
    // ========================================================================

    /// Send a simple transfer transaction
    pub async fn send_transfer(&self, from_index: usize, to: Address, value: U256) -> Result<B256> {
        let from = self.accounts[from_index];
        let wallet = self.wallet(from_index);

        let provider = ProviderBuilder::new()
            .wallet(wallet)
            .connect_http(self.endpoint_url());

        let tx = TransactionRequest::default()
            .with_from(from)
            .with_to(to)
            .with_value(value)
            .with_chain_id(self.chain_id)
            .with_gas_limit(21000)
            .with_max_fee_per_gas(20_000_000_000u128)
            .with_max_priority_fee_per_gas(1_000_000_000u128);

        let pending = provider.send_transaction(tx).await?;
        let tx_hash = pending.watch().await?;
        Ok(tx_hash)
    }
}

// ============================================================================
// Transaction Simulation Result
// ============================================================================

/// Result of a transaction simulation
#[derive(Debug)]
pub enum TransactionSimulationResult {
    /// Transaction succeeded when it should have failed
    UnexpectedSuccess,
    /// Transaction failed with expected error
    ExpectedError(String),
    /// Transaction is pending (not yet mined)
    Pending { tx_hash: B256, description: String },
    /// Transaction was reverted
    Reverted { tx_hash: B256, gas_used: u64 },
    /// Transaction was dropped from mempool
    Dropped { tx_hash: B256, was_dropped: bool },
}

impl TransactionSimulationResult {
    /// Check if the simulation resulted in an expected error
    pub fn is_expected_error(&self) -> bool {
        matches!(self, TransactionSimulationResult::ExpectedError(_))
    }

    /// Check if the simulation resulted in a reverted transaction
    pub fn is_reverted(&self) -> bool {
        matches!(self, TransactionSimulationResult::Reverted { .. })
    }
}

pub fn new_tx(from: Address, to: Address, value: U256) -> TransactionRequest {
    TransactionRequest::default()
        .with_from(from)
        .with_to(to)
        .with_value(value)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests;
