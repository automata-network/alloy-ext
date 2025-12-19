//! Error scenario tests for transaction submission flow.
//!
//! This module tests various error conditions that can occur during
//! the transaction submission process, organized by phase:
//!
//! - Phase 1: fill() errors (gas estimation, signing)
//! - Phase 2: send_transaction_inner() errors (nonce, network)
//! - Phase 3: get_receipt() errors (timeout, dropped)
//! - Phase 4: Execution results (revert)
//!
//! Test naming convention:
//! - `test_e{N}_{error_name}` - Single error scenario
//! - `test_r{N}_{result_name}` - Execution result scenario
//! - `test_{compound_scenario}` - Compound scenarios

use std::time::Duration;

use alloy::{
    network::TransactionBuilder,
    primitives::U256,
    providers::{ext::AnvilApi, Provider, ProviderBuilder},
};

use super::{new_tx, AnvilTestHarness};
use crate::ext::{classify_rpc_error, ProviderConfig, ProviderEx, RebroadcastConfig, RpcErrorKind};

// ============================================================================
// Phase 1: fill() Errors
// ============================================================================

/// E1: Gas estimation fails because contract reverts
///
/// Scenario: Send transaction to a contract that always reverts
/// Expected: fill() fails, nonce is released, subsequent tx uses same nonce
#[test_log::test(tokio::test)]
async fn test_e1_gas_estimation_revert() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.alice_provider();
    let alice = harness.alice();

    println!("\n=== E1: Gas Estimation Revert ===\n");

    // Deploy reverting contract
    let reverting_contract = harness.deploy_reverting_contract().await.unwrap();

    // Try to send transaction (without gas_limit, so it estimates)
    let tx = new_tx(alice, reverting_contract, U256::ZERO);

    let result = provider.send_transaction_ex(tx).await;
    assert!(result.is_err(), "Should fail during gas estimation");

    let error = result.err().unwrap().to_string().to_lowercase();
    assert!(
        error.contains("revert") || error.contains("execution"),
        "Error should indicate revert: {}",
        error
    );

    // Verify nonce was released
    let nonce_manager = provider.nonce_manager();
    let status = nonce_manager.get_status(alice).await;
    assert!(
        status.is_none(),
        "No nonce should be pending after gas estimation failure"
    );

    // Send a normal transaction - should use nonce 1 (previous one was released)
    // Note: harness.deploy_reverting_contract() uses a separate provider that consumed on-chain nonce 0
    // So our test provider initializes with next_nonce = 1 from chain
    let normal_tx = new_tx(alice, harness.bob(), U256::from(1000));

    let mut tracked = provider.send_transaction_ex(normal_tx).await.unwrap();
    assert_eq!(
        tracked.nonce(),
        1,
        "Should use nonce 1 (previous one was released after gas estimation failure)"
    );
    tracked.resolution().await.unwrap();

    println!("PASSED: Nonce correctly released after gas estimation revert\n");
}

/// E2: Gas estimation fails because of insufficient funds
///
/// Scenario: Send value exceeding account balance
/// Expected: fill() fails, nonce is released
#[test_log::test(tokio::test)]
async fn test_e2_gas_estimation_insufficient_funds() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.alice_provider();
    let alice = harness.alice();
    harness.set_nonce(alice, 1).await.unwrap();

    println!("\n=== E2: Gas Estimation Insufficient Funds ===\n");

    // Get current balance
    let balance = harness.get_balance(alice).await.unwrap();
    println!("Alice balance: {} wei", balance);

    // Try to send more than balance
    let tx = new_tx(alice, harness.bob(), balance + U256::from(1));

    let result = provider.send_transaction_ex(tx).await;
    assert!(result.is_err(), "Should fail due to insufficient funds");

    let error = result.err().unwrap().to_string().to_lowercase();
    println!("Error: {}", error);
    assert!(
        error.contains("insufficient") || error.contains("funds") || error.contains("balance"),
        "Error should indicate insufficient funds: {}",
        error
    );

    // Verify nonce was released
    let status = provider.nonce_manager().get_status(alice).await.unwrap();
    assert!(
        status.pending_nonces.is_empty() && status.base_nonce == 1,
        "No nonce should be pending after insufficient funds error"
    );

    println!("PASSED: Nonce correctly released after insufficient funds\n");
}

// ============================================================================
// Phase 2: send_transaction_inner() Errors
// ============================================================================

/// E4: Nonce too low - local nonce behind chain
///
/// Scenario: Another process sent transactions, our nonce is stale
/// Expected: auto_recovery syncs and retries successfully
#[test_log::test(tokio::test)]
async fn test_e4_nonce_too_low_recovery() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.alice_provider();
    let alice = harness.alice();

    println!("\n=== E4: Nonce Too Low Recovery ===\n");

    // Initialize nonce manager by sending a tx (uses nonce 0, next_nonce becomes 1)
    let mut init_tx = provider
        .send_transaction_ex(new_tx(alice, harness.bob(), U256::ZERO))
        .await
        .unwrap();
    init_tx.resolution().await.unwrap();

    // Simulate external transactions: set on-chain nonce to 10
    // Our nonce manager still thinks next_nonce = 1
    harness.set_nonce(alice, 10).await.unwrap();

    // Send new tx - should fail with nonce_too_low (local=1, chain=10)
    // Then sync and retry with nonce 10
    let tx = new_tx(alice, harness.bob(), U256::from(3000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let used_nonce = tracked.nonce();
    println!("Our tx used nonce: {}", used_nonce);

    assert_eq!(used_nonce, 10, "Should use nonce 10 after sync");

    let _receipt = tracked.resolution().await.unwrap();
    println!("PASSED: Auto recovery handled nonce too low correctly\n");
}

/// E6: Already known - our error classification handles AlreadyKnown correctly
///
/// Scenario: Send tx, rebroadcast the same signed tx
/// Expected: Rebroadcast returns AlreadyKnown which is handled gracefully
#[test_log::test(tokio::test)]
async fn test_e6_already_known() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();
    let provider = harness.alice_provider();
    let new_provider = harness.new_provider(Some(alice)).await.unwrap();

    println!("\n=== E6: Already Known ===\n");

    // Disable automine to keep tx in mempool
    harness.disable_automine().await.unwrap();

    // Send tx through our provider
    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let tracked = provider.send_transaction_ex(tx.clone()).await.unwrap();
    let tx_hash = tracked.tx_hash();
    println!("First send successful, tx_hash: {}", tx_hash);

    let result = new_provider.send_transaction_ex(tx).await;

    match result {
        Ok(_) => {
            println!("Rebroadcast accepted (node allows duplicates)");
        }
        Err(e) => {
            // Verify our error classification works
            let kind = classify_rpc_error(&e);
            assert_eq!(
                kind,
                RpcErrorKind::AlreadyKnown,
                "Should classify as AlreadyKnown, got: {:?}",
                kind
            );
        }
    }

    // Enable automine and verify the original tx can still be confirmed
    harness.enable_automine().await.unwrap();
    harness.mine_block().await.unwrap();

    // The tracked tx should still work - drop it to avoid hanging
    drop(tracked);

    println!("PASSED: AlreadyKnown error handled correctly\n");
}

/// E7: Replacement underpriced - error classification for replacement errors
///
/// Scenario: Try to replace mempool tx with lower gas price
/// Expected: Error is classified as ReplacementUnderpriced
#[test_log::test(tokio::test)]
async fn test_e7_replacement_underpriced() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== E7: Replacement Underpriced ===\n");

    harness.disable_automine().await.unwrap();

    // Use raw provider to trigger the actual RPC error
    let wallet = harness.wallet(0);
    let raw_provider = ProviderBuilder::new()
        .wallet(wallet)
        .connect_http(harness.endpoint().parse::<reqwest::Url>().unwrap());

    // Send with high gas price
    let tx1 = new_tx(alice, harness.bob(), U256::from(1000))
        .with_nonce(0u64)
        .with_chain_id(harness.chain_id())
        .with_gas_limit(21000)
        .with_max_fee_per_gas(50_000_000_000u128)
        .with_max_priority_fee_per_gas(5_000_000_000u128);

    let _pending = raw_provider.send_transaction(tx1).await.unwrap();
    println!("First tx sent with high gas price");

    // Try to replace with lower gas price
    let tx2 = new_tx(alice, harness.bob(), U256::from(2000))
        .with_nonce(0u64) // Same nonce
        .with_chain_id(harness.chain_id())
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128) // Lower
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let result = raw_provider.send_transaction(tx2).await;

    match result {
        Ok(_) => {
            println!("Second tx accepted (Anvil may not enforce replacement pricing)");
        }
        Err(e) => {
            // Verify our error classification works
            let kind = classify_rpc_error(&e);
            println!("Error: {}", e);
            println!("Classified as: {:?}", kind);
            assert_eq!(
                kind,
                RpcErrorKind::ReplacementUnderpriced,
                "Should classify as ReplacementUnderpriced, got: {:?}",
                kind
            );
        }
    }

    harness.enable_automine().await.unwrap();
    println!("PASSED: Replacement underpriced error classification correct\n");
}

// ============================================================================
// Phase 3: get_receipt() Errors
// ============================================================================

/// E11: Timeout - transaction not confirmed in time
///
/// Scenario: Transaction sent but automine disabled, times out
/// Expected: Nonce marked as abandoned after timeout
#[test_log::test(tokio::test)]
async fn test_e11_receipt_timeout() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== E11: Receipt Timeout ===\n");

    // Create provider with short timeout
    let provider = harness
        .alice_provider()
        .with_receipt_timeout(Duration::from_millis(100));

    // Disable automine
    harness.disable_automine().await.unwrap();

    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let nonce = tracked.nonce();
    let tx_hash = tracked.tx_hash();
    println!("Tx sent with nonce {} hash {}", nonce, tx_hash);

    // get_receipt should timeout (automine is disabled)
    let state = tracked.resolution().await.unwrap();
    assert!(state.is_timeout(), "Should be Timeout state");
    println!("Receipt timeout as expected, state: {:?}", state.is_timeout());

    // Nonce should be abandoned
    let nonce_manager = provider.nonce_manager();
    let status = nonce_manager.get_status(alice).await.unwrap();
    println!("Nonce status: abandoned={:?}", status.abandoned_nonces);
    assert!(
        status.abandoned_nonces.contains(&nonce),
        "Nonce should be abandoned after timeout"
    );

    harness.enable_automine().await.unwrap();
    println!("PASSED: Timeout correctly marks nonce as abandoned\n");

    // TODO: should we test proactive recovery here?
}

/// E12a: Transaction dropped from mempool (no rebroadcast)
///
/// Scenario: Transaction sent, dropped from mempool, no rebroadcast
/// Expected: Times out and marks nonce as abandoned
#[test_log::test(tokio::test)]
async fn test_e12a_transaction_dropped_no_recovery() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== E12a: Transaction Dropped (No Recovery) ===\n");

    // Create provider with NO rebroadcast - dropped tx stays dropped
    let provider = harness
        .alice_provider()
        .with_receipt_timeout(Duration::from_millis(100))
        .with_config(ProviderConfig::default().with_rebroadcast(RebroadcastConfig::disabled()));

    harness.disable_automine().await.unwrap();

    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let nonce = tracked.nonce();
    let tx_hash = tracked.tx_hash();
    println!("Tx sent with nonce {} hash {}", nonce, tx_hash);

    // Drop from mempool - tx won't be rebroadcast so it stays dropped
    harness.drop_transaction(tx_hash).await.unwrap();
    println!("Transaction dropped from mempool");

    // get_receipt should timeout since tx is gone and no rebroadcast
    let state = tracked.resolution().await.unwrap();
    assert!(state.is_timeout(), "Should be Timeout state after tx dropped");

    // Nonce should be abandoned (auto_recovery checks chain and marks abandoned)
    let status = provider.nonce_manager().get_status(alice).await.unwrap();
    assert!(
        status.abandoned_nonces.contains(&nonce),
        "Nonce should be abandoned, got: {:?}",
        status
    );

    println!("PASSED: Dropped transaction correctly marked as abandoned\n");
}

/// E12b: Transaction dropped from mempool but recovered via rebroadcast
///
/// Scenario: Transaction sent, dropped from mempool, rebroadcast recovers it
/// Expected: Rebroadcast re-adds tx to mempool, tx gets mined successfully
#[test_log::test(tokio::test)]
async fn test_e12b_transaction_dropped_with_recovery() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== E12b: Transaction Dropped (With Recovery) ===\n");

    // Create provider with rebroadcast enabled (fast interval for testing)
    let provider = harness
        .alice_provider()
        .with_receipt_timeout(Duration::from_secs(2))
        .with_config(ProviderConfig::default().with_rebroadcast(
            RebroadcastConfig::default().with_interval(Duration::from_millis(50)),
        ));

    harness.disable_automine().await.unwrap();

    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let nonce = tracked.nonce();
    let tx_hash = tracked.tx_hash();
    println!("Tx sent with nonce {} hash {}", nonce, tx_hash);

    // Drop from mempool
    harness.drop_transaction(tx_hash).await.unwrap();
    println!("Transaction dropped from mempool");

    // Enable automine - rebroadcast will re-add tx, then it gets mined
    harness.enable_automine().await.unwrap();

    // Should succeed - rebroadcast recovers the dropped tx
    let state = tracked.resolution().await.unwrap();
    let receipt = state.receipt().expect("Should have receipt");
    println!("Receipt received, status: {}", receipt.status());
    assert!(receipt.status(), "Transaction should succeed");

    // Nonce should be confirmed, not abandoned
    assert!(
        state.is_success(),
        "Nonce should be confirmed after recovery"
    );

    println!("PASSED: Dropped transaction recovered via rebroadcast\n");
}

/// E13: Transaction marked abandoned but actually confirmed on chain
///
/// Scenario: tx times out locally (marked abandoned), but was actually mined
/// Expected: Next send detects nonce_too_low, syncs and uses correct nonce
#[test_log::test(tokio::test)]
async fn test_e13_abandoned_but_confirmed() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== E13: Abandoned But Actually Confirmed ===\n");

    // Create provider with very short timeout and NO rebroadcast
    let provider = harness
        .alice_provider()
        .with_receipt_timeout(Duration::from_millis(50))
        .with_config(ProviderConfig::default().with_rebroadcast(RebroadcastConfig::disabled()));

    harness.disable_automine().await.unwrap();

    // Send tx - will timeout because automine is off
    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let nonce = tracked.nonce();
    let tx_hash = tracked.tx_hash();
    println!("Tx sent with nonce {} hash {}", nonce, tx_hash);

    // get_receipt times out - nonce marked as abandoned
    let state = tracked.resolution().await.unwrap();
    assert!(state.is_timeout(), "Should be Timeout state");

    let status = provider.nonce_manager().get_status(alice).await.unwrap();
    assert!(
        status.abandoned_nonces.contains(&nonce),
        "Nonce should be abandoned"
    );
    println!(
        "Nonce {} marked as abandoned (but tx still in mempool)",
        nonce
    );

    // Now mine the block - tx actually gets confirmed!
    harness.enable_automine().await.unwrap();
    harness.mine_block().await.unwrap();
    println!("Block mined - tx actually confirmed on chain");

    // Try to send next tx - should detect nonce_too_low and recover
    let tx2 = new_tx(alice, harness.bob(), U256::from(2000));
    let tracked2 = provider.send_transaction_ex(tx2).await.unwrap();

    // Should use nonce 1 (after syncing with chain)
    assert_eq!(
        tracked2.nonce(),
        nonce + 1,
        "Should use nonce {} after recovery, got {}",
        nonce + 1,
        tracked2.nonce()
    );

    println!("PASSED: Recovered from abandoned-but-confirmed state\n");
}

// ============================================================================
// Phase 4: Execution Results
// ============================================================================

/// R2: Transaction reverts - tx mined but execution fails
///
/// Scenario: Call contract that reverts (with manual gas_limit)
/// Expected: Transaction confirmed (nonce used), but status = 0
#[test_log::test(tokio::test)]
async fn test_r2_transaction_revert() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.alice_provider();
    let alice = harness.alice();

    println!("\n=== R2: Transaction Revert ===\n");

    // Deploy reverting contract
    let reverting_contract = harness.deploy_reverting_contract().await.unwrap();

    // Send with manual gas_limit (bypass estimation)
    let tx = new_tx(alice, reverting_contract, U256::ZERO).with_gas_limit(100000);

    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let nonce = tracked.nonce();
    println!("Tx sent with nonce {}", nonce);

    let state = tracked.resolution().await.unwrap();
    let receipt = state.receipt().expect("Should have receipt");
    println!("Receipt received, status: {}", receipt.status());

    // Tx mined but reverted (status = 0)
    assert!(
        !receipt.status(),
        "Transaction should have reverted (status=0)"
    );

    // Nonce should be confirmed (even if reverted, nonce is used)
    let status = provider.nonce_manager().get_status(alice).await.unwrap();
    assert!(
        status.confirmed(nonce),
        "Nonce should be confirmed (not pending / abandoned)"
    );

    // Next tx should use nonce + 1
    let next_tx = new_tx(alice, harness.bob(), U256::from(1000));
    let tracked2 = provider.send_transaction_ex(next_tx).await.unwrap();
    assert_eq!(tracked2.nonce(), nonce + 1, "Next tx should use nonce + 1");

    println!("PASSED: Reverted transaction correctly confirmed nonce\n");
}

// ============================================================================
// Compound Scenarios
// ============================================================================

/// Compound: Concurrent sends with middle failure
///
/// Scenario: Send tx0, tx1 (fails estimation), tx2 sequentially
/// Expected: tx1's nonce released, tx2 uses nonce 1
#[test_log::test(tokio::test)]
async fn test_concurrent_with_failure() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.alice_provider();
    let alice = harness.alice();

    println!("\n=== Concurrent with Failure ===\n");

    // Note: deploy_reverting_contract uses on-chain nonce 0 via separate provider
    let reverting_contract = harness.deploy_reverting_contract().await.unwrap();

    // tx0: test provider sees on-chain nonce = 1 after deployment
    let tx0 = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked0 = provider.send_transaction_ex(tx0).await.unwrap();
    assert_eq!(tracked0.nonce(), 1);
    println!("tx0 sent with nonce 1");

    // tx1: will fail (gas estimation revert) - allocates nonce 2, then releases
    let tx1_revert = new_tx(alice, reverting_contract, U256::ZERO);
    let result1 = provider.send_transaction_ex(tx1_revert).await;
    assert!(result1.is_err(), "tx1 should fail (gas estimation revert)");
    println!("tx1 failed as expected (gas estimation)");

    // tx2: should use nonce 2 (tx1's nonce was released)
    let tx2 = new_tx(alice, harness.bob(), U256::from(2000));

    let mut tracked2 = provider.send_transaction_ex(tx2).await.unwrap();
    assert_eq!(
        tracked2.nonce(),
        2,
        "tx2 should use nonce 2 (tx1's nonce was released)"
    );
    println!("tx2 sent with nonce 2");

    // Confirm both
    tracked0.resolution().await.unwrap();
    tracked2.resolution().await.unwrap();

    println!("PASSED: Concurrent transactions with failure handled correctly\n");
}

/// Compound: Gap recovery and continue
///
/// Scenario: Create gap by abandoning tx1, then send new tx triggers recovery
/// Expected: Gap filled, new tx succeeds
#[test_log::test(tokio::test)]
async fn test_gap_recovery_and_continue() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.alice_provider();
    let alice = harness.alice();

    println!("\n=== Gap Recovery and Continue ===\n");

    // Send and confirm tx0
    let tx0 = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked0 = provider.send_transaction_ex(tx0).await.unwrap();
    assert_eq!(tracked0.nonce(), 0);
    tracked0.resolution().await.unwrap();
    println!("tx0 (nonce 0) confirmed");

    // Send tx1 but abandon it (create gap)
    harness.disable_automine().await.unwrap();
    let tx1 = new_tx(alice, harness.bob(), U256::from(2000));
    let tracked1 = provider.send_transaction_ex(tx1).await.unwrap();
    let tx1_hash = tracked1.tx_hash();
    assert_eq!(tracked1.nonce(), 1);
    println!("tx1 (nonce 1) sent");

    // Drop and abandon
    harness.drop_transaction(tx1_hash).await.unwrap();
    drop(tracked1);
    println!("tx1 dropped and abandoned - gap created");

    harness.enable_automine().await.unwrap();

    // Verify gap exists
    let status = provider.nonce_manager().get_status(alice).await.unwrap();
    assert!(
        status.abandoned_nonces.contains(&1),
        "Nonce 1 should be abandoned"
    );

    // Send new tx - should trigger proactive recovery
    let tx2 = new_tx(alice, harness.bob(), U256::from(3000));
    let mut tracked2 = provider.send_transaction_ex(tx2).await.unwrap();
    println!("tx2 sent with nonce {}", tracked2.nonce());

    tracked2.resolution().await.unwrap();

    // Verify gap filled
    let final_status = provider.nonce_manager().get_status(alice).await.unwrap();
    assert!(
        final_status.abandoned_nonces.is_empty(),
        "No abandoned nonces should remain"
    );

    let on_chain_nonce = harness.get_nonce(alice).await.unwrap();
    println!("Final on-chain nonce: {}", on_chain_nonce);
    assert!(on_chain_nonce >= 2, "On-chain nonce should be at least 2");

    println!("PASSED: Gap recovery and continue successful\n");
}

// ============================================================================
// TxResolution Integration Tests
// ============================================================================

/// TxResolution::Confirmed - Normal transaction confirmation
///
/// Tests that a successfully mined transaction:
/// - Returns TxResolution::Confirmed
/// - is_success() returns true
/// - receipt() returns the original TX receipt
/// - cancel_receipt() returns None
#[test_log::test(tokio::test)]
async fn test_txstate_confirmed() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.alice_provider();
    let alice = harness.alice();

    println!("\n=== TxResolution::Confirmed ===\n");

    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let original_tx_hash = tracked.tx_hash();
    println!("TX sent with hash: {}", original_tx_hash);

    // Get receipt - should succeed normally
    let state = tracked.resolution().await.unwrap();

    // Verify state (TxResolution is always resolved, so no is_pending/is_resolved checks)
    assert!(state.is_success(), "Should be success");
    assert!(!state.is_cancelled(), "Should not be cancelled");
    assert!(!state.is_timeout(), "Should not be timeout");

    // Verify receipt() returns original TX receipt
    let receipt = state.receipt().expect("Should have receipt");
    assert_eq!(
        receipt.transaction_hash, original_tx_hash,
        "receipt() should return original TX hash"
    );
    assert!(receipt.status(), "TX should have succeeded");

    // Verify cancel_receipt() returns None
    assert!(
        state.cancel_receipt().is_none(),
        "cancel_receipt() should be None for Confirmed"
    );

    // Verify cancel_tx_hash() returns None
    assert!(
        state.cancel_tx_hash().is_none(),
        "cancel_tx_hash() should be None for Confirmed"
    );

    println!("PASSED: TxResolution::Confirmed verified\n");
}

/// TxResolution::Cancelled - Cancel TX wins the race
///
/// Tests that when cancel TX is mined (original replaced):
/// - Returns TxResolution::Cancelled
/// - is_success() returns false
/// - is_cancelled() returns true
/// - receipt() returns None (original was NOT confirmed)
/// - cancel_receipt() returns the cancel TX receipt
#[test_log::test(tokio::test)]
async fn test_txstate_cancelled() {
    use crate::ext::CancelConfig;

    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== TxResolution::Cancelled ===\n");

    // Short Phase 1 timeout, longer Phase 2 timeout for racing
    // Use high gas multiplier to ensure cancel TX replaces original
    let provider = harness
        .alice_provider()
        .with_receipt_timeout(Duration::from_millis(100))
        .with_config(
            ProviderConfig::default()
                .with_cancel(CancelConfig::default().with_gas_multiplier(2.0))
                .with_rebroadcast(RebroadcastConfig::disabled()),
        );

    // Disable automine to prevent immediate confirmation
    harness.disable_automine().await.unwrap();

    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let original_tx_hash = tracked.tx_hash();
    let nonce = tracked.nonce();
    println!("Original TX sent: {} (nonce {})", original_tx_hash, nonce);

    // Spawn a background task to enable automine after Phase 1 timeout
    let harness_endpoint = harness.endpoint().to_string();
    tokio::spawn(async move {
        // Wait for Phase 1 to timeout and cancel TX to be sent
        tokio::time::sleep(Duration::from_millis(150)).await;
        // Enable automine via RPC
        let provider = ProviderBuilder::new().connect_http(harness_endpoint.parse().unwrap());
        let _ = provider.anvil_set_auto_mine(true).await;
        let _ = provider.anvil_mine(Some(1u64), None).await;
    });

    // Call get_receipt - this will:
    // 1. Phase 1 timeout (automine is off)
    // 2. Send cancel TX with higher gas
    // 3. Background task enables automine
    // 4. Cancel TX gets mined (it replaced original with higher gas)
    let state = tracked.resolution().await.unwrap();

    // The state should be Cancelled or Timeout
    if state.is_cancelled() {
        println!("Got TxResolution::Cancelled as expected");

        // TxResolution is always resolved, so no is_pending/is_resolved checks
        assert!(!state.is_success(), "Should NOT be success (original not confirmed)");
        assert!(state.is_cancelled(), "Should be cancelled");
        assert!(!state.is_timeout(), "Should not be timeout");

        // receipt() should return Err - original TX was NOT confirmed
        assert!(
            state.receipt().is_err(),
            "receipt() should be Err for Cancelled (original not confirmed)"
        );

        // cancel_receipt() should return the cancel TX receipt
        let cancel_receipt = state.cancel_receipt().expect("Should have cancel_receipt");
        assert!(cancel_receipt.status(), "Cancel TX should have succeeded");
        assert_ne!(
            cancel_receipt.transaction_hash, original_tx_hash,
            "cancel_receipt should NOT be original TX"
        );
        println!("Cancel TX hash: {}", cancel_receipt.transaction_hash);

        println!("PASSED: TxResolution::Cancelled verified\n");
    } else if state.is_timeout() {
        // If timing is tight, we might get Timeout
        println!("Got Timeout (timing race) - this is acceptable");
    } else if state.is_success() {
        // Original might have won if timing was off
        println!("Got success - original was mined before cancel");
    } else {
        panic!("Unexpected state");
    }

    harness.enable_automine().await.unwrap();
}

/// TxResolution::Timeout - Both TXs timeout
///
/// Tests that when neither TX confirms:
/// - Returns TxResolution::Timeout
/// - is_success() returns false
/// - is_timeout() returns true
/// - receipt() returns None
/// - cancel_receipt() returns None
/// - cancel_tx_hash() returns Some (cancel TX was sent)
#[test_log::test(tokio::test)]
async fn test_txstate_double_timeout() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== TxResolution::Timeout ===\n");

    // Very short timeouts
    let provider = harness
        .alice_provider()
        .with_receipt_timeout(Duration::from_millis(100));

    // Disable automine - neither TX will confirm
    harness.disable_automine().await.unwrap();

    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let original_tx_hash = tracked.tx_hash();
    println!("Original TX sent: {}", original_tx_hash);

    // get_receipt will timeout both phases
    let state = tracked.resolution().await.unwrap();

    // Verify state
    assert!(!state.is_success(), "Should NOT be success");
    assert!(!state.is_cancelled(), "Should not be cancelled");
    assert!(state.is_timeout(), "Should be timeout");

    // receipt() should return Err
    assert!(
        state.receipt().is_err(),
        "receipt() should be Err for Timeout"
    );

    // cancel_receipt() should return None
    assert!(
        state.cancel_receipt().is_none(),
        "cancel_receipt() should be None for Timeout"
    );

    // cancel_tx_hash() should return Some (cancel TX was sent but not confirmed)
    let cancel_hash = state.cancel_tx_hash();
    assert!(
        cancel_hash.is_some(),
        "cancel_tx_hash() should be Some for Timeout"
    );
    println!("Cancel TX hash: {}", cancel_hash.unwrap());

    // Verify nonce is abandoned
    let status = provider.nonce_manager().get_status(alice).await.unwrap();
    assert!(
        status.abandoned_nonces.contains(&tracked.nonce()),
        "Nonce should be abandoned after Timeout"
    );

    harness.enable_automine().await.unwrap();
    println!("PASSED: TxResolution::Timeout verified\n");
}

/// TxResolution::OriginalConfirmedAfterCancel - Original wins race after cancel sent
///
/// This scenario requires the original TX to be mined while the cancel TX
/// is still pending. In practice, this happens when:
/// - Original TX is already being processed when cancel arrives
/// - Cancel TX fails to propagate to miners in time
///
/// With Anvil's EIP-1559 replacement semantics, the cancel TX (higher gas)
/// normally replaces the original. We attempt to simulate OriginalConfirmedAfterCancel
/// by using a very low gas multiplier (1.01) which may not be enough to replace.
#[test_log::test(tokio::test)]
async fn test_txstate_original_confirmed_after_cancel() {
    use crate::ext::CancelConfig;

    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    println!("\n=== TxResolution::OriginalConfirmedAfterCancel ===\n");

    // Use very low gas multiplier - cancel TX may fail to replace original
    // This gives us a chance to get OriginalConfirmedAfterCancel
    let provider = harness
        .alice_provider()
        .with_receipt_timeout(Duration::from_millis(100))
        .with_config(
            ProviderConfig::default()
                .with_cancel(CancelConfig::default().with_gas_multiplier(1.01))
                .with_rebroadcast(RebroadcastConfig::disabled()),
        );

    // Disable automine
    harness.disable_automine().await.unwrap();

    let tx = new_tx(alice, harness.bob(), U256::from(1000));
    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let original_tx_hash = tracked.tx_hash();
    println!("Original TX sent: {}", original_tx_hash);

    // Spawn a background task to enable automine after Phase 1 timeout
    let harness_endpoint = harness.endpoint().to_string();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(150)).await;
        let provider = ProviderBuilder::new().connect_http(harness_endpoint.parse().unwrap());
        let _ = provider.anvil_set_auto_mine(true).await;
        let _ = provider.anvil_mine(Some(1u64), None).await;
    });

    // Call get_receipt
    let state = tracked.resolution().await.unwrap();

    // Due to replacement semantics, we'll likely get Cancelled
    // But with low gas multiplier, we might get OriginalConfirmedAfterCancel
    if state.is_success() && state.cancel_tx_hash().is_some() {
        println!("Got OriginalConfirmedAfterCancel!");

        let receipt = state.receipt().expect("Should have receipt");
        assert_eq!(
            receipt.transaction_hash, original_tx_hash,
            "receipt() should return original TX"
        );

        let cancel_hash = state.cancel_tx_hash().unwrap();
        println!("Cancel TX was sent but original won: {}", cancel_hash);

        assert!(
            state.cancel_receipt().is_none(),
            "cancel_receipt() should be None (cancel not confirmed)"
        );

        println!("PASSED: TxResolution::OriginalConfirmedAfterCancel verified\n");
    } else if state.is_success() {
        // This is just Confirmed (cancel TX was never sent or Phase 1 succeeded)
        println!("Got Confirmed - no cancel TX was sent");
    } else if state.is_cancelled() {
        // Cancel TX won the race (expected with replacement semantics)
        println!("Got Cancelled - cancel TX replaced original and was mined");
        println!("This is expected behavior with EIP-1559 replacement");

        // Still verify the Cancelled state is correct
        assert!(state.receipt().is_err(), "receipt() should be Err for Cancelled");
        assert!(state.cancel_receipt().is_some(), "cancel_receipt() should exist");
    } else if state.is_timeout() {
        println!("Got Timeout - neither TX was mined in time");
    }

    harness.enable_automine().await.unwrap();
}
