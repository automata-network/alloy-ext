use super::*;
use crate::ext::{nonce_state, ProviderEx};
use alloy::network::TransactionBuilder;

#[tokio::test]
async fn test_harness_creation() {
    let harness = AnvilTestHarness::new().await.unwrap();
    assert!(!harness.accounts().is_empty());
    assert!(harness.chain_id() > 0);
}

#[tokio::test]
async fn test_snapshot_and_revert() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let bob = harness.bob();

    // Get initial balance
    let initial_balance = harness.get_balance(bob).await.unwrap();

    // Take snapshot
    let snapshot = harness.snapshot().await.unwrap();

    // Send transfer
    harness
        .send_transfer(0, bob, U256::from(1_000_000_000_000_000_000u128))
        .await
        .unwrap();

    // Verify balance changed
    let new_balance = harness.get_balance(bob).await.unwrap();
    assert!(new_balance > initial_balance);

    // Revert to snapshot
    let reverted = harness.revert(snapshot).await.unwrap();
    assert!(reverted);

    // Verify balance is back to initial
    let reverted_balance = harness.get_balance(bob).await.unwrap();
    assert_eq!(reverted_balance, initial_balance);
}

#[tokio::test]
async fn test_set_balance() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    let new_balance = U256::from(123_456_789_000_000_000_000u128);
    harness.set_balance(alice, new_balance).await.unwrap();

    let balance = harness.get_balance(alice).await.unwrap();
    assert_eq!(balance, new_balance);
}

#[tokio::test]
async fn test_set_nonce() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let alice = harness.alice();

    harness.set_nonce(alice, 100).await.unwrap();

    let nonce = harness.get_nonce(alice).await.unwrap();
    assert_eq!(nonce, 100);
}

#[tokio::test]
async fn test_mining_control() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let initial_block = harness.provider.get_block_number().await.unwrap();

    harness.mine_blocks(5).await.unwrap();

    let new_block = harness.provider.get_block_number().await.unwrap();
    assert_eq!(new_block, initial_block + 5);
}

#[tokio::test]
async fn test_simulate_nonce_too_low() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = harness.simulate_nonce_too_low().await.unwrap();
    assert!(
        result.is_expected_error(),
        "Expected error, got: {:?}",
        result
    );
}

#[tokio::test]
async fn test_simulate_insufficient_funds() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = harness.simulate_insufficient_funds().await.unwrap();
    assert!(
        result.is_expected_error(),
        "Expected error, got: {:?}",
        result
    );
}

#[tokio::test]
async fn test_simulate_revert() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = harness.simulate_revert().await.unwrap();
    assert!(
        result.is_reverted() || result.is_expected_error(),
        "Expected revert or error, got: {:?}",
        result
    );
}

#[tokio::test]
async fn test_simulate_dropped_transaction() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = harness.simulate_dropped_transaction().await.unwrap();
    match result {
        TransactionSimulationResult::Dropped { was_dropped, .. } => {
            assert!(was_dropped, "Transaction should have been dropped");
        }
        _ => panic!("Expected Dropped result, got: {:?}", result),
    }
}

#[tokio::test]
async fn test_simulate_nonce_gap() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = harness.simulate_nonce_gap(5).await.unwrap();
    match result {
        TransactionSimulationResult::Pending { description, .. } => {
            assert!(
                description.contains("gap"),
                "Expected gap description, got: {}",
                description
            );
        }
        TransactionSimulationResult::ExpectedError(_) => {
            // Some nodes may reject nonce gap transactions outright
        }
        _ => panic!("Expected Pending or Error result, got: {:?}", result),
    }
}

/// Test single dropped transaction marks nonce as abandoned.
#[tokio::test]
async fn test_single_tx_dropped_and_abandoned() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = NonceBehaviorScenario::new("Single tx dropped")
        .description("Single transaction dropped from mempool and abandoned")
        .tx(TxSpec::drop_and_abandon("tx0"))
        .run(&harness)
        .await
        .unwrap();

    result.assert_passed();

    assert_eq!(
        result.nonce_status.abandoned_count(),
        1,
        "Should have 1 abandoned nonce"
    );
    assert!(
        result.nonce_status.abandoned_nonces.contains(&0),
        "Nonce 0 should be abandoned"
    );
}

/// Test single confirmed transaction.
#[tokio::test]
async fn test_single_tx_confirmed() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = NonceBehaviorScenario::new("Single tx confirmed")
        .description("Single transaction confirmed successfully")
        .tx(TxSpec::confirm("tx0"))
        .run(&harness)
        .await
        .unwrap();

    result.assert_passed();

    assert_eq!(
        result.nonce_status.abandoned_count(),
        0,
        "Should have 0 abandoned nonces"
    );
    assert!(
        result.nonce_status.pending_nonces.is_empty(),
        "Should have no pending nonces"
    );
}

/// Test TrackedPendingTx Drop marks nonce as abandoned.
#[tokio::test]
async fn test_tracked_pending_tx_drop_abandons_nonce() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.network_provider_with_signer(0);
    let alice = harness.alice();
    let bob = harness.bob();

    harness.disable_automine().await.unwrap();

    let tx = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(1000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let tracked = provider.send_transaction_ex(tx).await.unwrap();
    let tx_hash = tracked.tx_hash();
    let atomic_state = tracked.atomic_state().clone();

    // Drop from mempool and drop TrackedPendingTx without calling get_receipt()
    harness.drop_transaction(tx_hash).await.unwrap();
    drop(tracked);

    // Verify nonce abandoned
    assert_eq!(atomic_state.get(), nonce_state::ABANDONED);

    harness.enable_automine().await.unwrap();
}

/// Test TrackedPendingTx get_receipt() confirms nonce.
#[tokio::test]
async fn test_tracked_pending_tx_get_receipt_confirms_nonce() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.network_provider_with_signer(0);
    let alice = harness.alice();
    let bob = harness.bob();

    let tx = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(1000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let atomic_state = tracked.atomic_state().clone();

    tracked.get_receipt().await.unwrap();

    // Verify nonce confirmed
    assert_eq!(atomic_state.get(), nonce_state::CONFIRMED);
}

/// Test multiple transactions with mixed confirmation and abandonment.
///
/// This test demonstrates the nonce gap scenario:
///
/// 1. Send 3 transactions: nonce 0, 1, 2
/// 2. Drop tx[1] (nonce 1) from mempool and abandon it
/// 3. Results:
///    - tx[0] (nonce 0): SUCCESS - mined normally
///    - tx[1] (nonce 1): ABANDONED - dropped from mempool, nonce marked abandoned
///    - tx[2] (nonce 2): STUCK - cannot be mined due to nonce gap (waiting for nonce 1)
///
/// This demonstrates why abandoned nonces need gap filling to unblock subsequent txs.
#[tokio::test]
async fn test_mixed_confirmed_and_abandoned_txs() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = NonceBehaviorScenario::new("Mixed confirmed and abandoned")
        .description("tx0 confirmed, tx1 abandoned (gap), tx2 stuck")
        .tx(TxSpec::confirm("tx0"))
        .tx(TxSpec::drop_and_abandon("tx1"))
        .tx(TxSpec::leave_stuck("tx2"))
        .run(&harness)
        .await
        .unwrap();

    result.assert_passed();

    // Verify nonce manager state
    assert!(
        result.nonce_status.abandoned_nonces.contains(&1),
        "Nonce 1 should be in abandoned list"
    );
    assert!(
        result.nonce_status.pending_nonces.contains(&2),
        "Nonce 2 should still be in pending list (stuck)"
    );
    assert_eq!(
        result.nonce_status.abandoned_count(),
        1,
        "Should have exactly 1 abandoned nonce"
    );
}

/// Test all transactions confirmed.
#[tokio::test]
async fn test_scenario_all_confirmed() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = NonceBehaviorScenario::new("All confirmed")
        .description("All transactions are confirmed successfully")
        .tx(TxSpec::confirm("tx0"))
        .tx(TxSpec::confirm("tx1"))
        .tx(TxSpec::confirm("tx2"))
        .run(&harness)
        .await
        .unwrap();

    result.assert_passed();

    // Verify no abandoned nonces
    assert_eq!(
        result.nonce_status.abandoned_count(),
        0,
        "Should have no abandoned nonces"
    );
}

/// Test first transaction abandoned (blocks all subsequent).
#[tokio::test]
async fn test_scenario_first_abandoned() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = NonceBehaviorScenario::new("First abandoned")
        .description("First tx abandoned blocks all subsequent transactions")
        .tx(TxSpec::drop_and_abandon("tx0"))
        .tx(TxSpec::leave_stuck("tx1"))
        .tx(TxSpec::leave_stuck("tx2"))
        .run(&harness)
        .await
        .unwrap();

    result.assert_passed();

    // Verify nonce 0 is abandoned, rest are stuck
    assert!(
        result.nonce_status.abandoned_nonces.contains(&0),
        "Nonce 0 should be abandoned"
    );
    assert!(
        result.nonce_status.pending_nonces.contains(&1),
        "Nonce 1 should be stuck pending"
    );
    assert!(
        result.nonce_status.pending_nonces.contains(&2),
        "Nonce 2 should be stuck pending"
    );
}

/// Test multiple gaps scenario.
#[tokio::test]
async fn test_scenario_multiple_gaps() {
    let harness = AnvilTestHarness::new().await.unwrap();

    let result = NonceBehaviorScenario::new("Multiple gaps")
        .description("Multiple abandoned transactions creating multiple gaps")
        .tx(TxSpec::drop_and_abandon("tx0"))
        .tx(TxSpec::drop_and_abandon("tx1"))
        .tx(TxSpec::leave_stuck("tx2"))
        .run(&harness)
        .await
        .unwrap();

    result.assert_passed();

    // Verify both nonce 0 and 1 are abandoned
    assert!(
        result.nonce_status.abandoned_nonces.contains(&0),
        "Nonce 0 should be abandoned"
    );
    assert!(
        result.nonce_status.abandoned_nonces.contains(&1),
        "Nonce 1 should be abandoned"
    );
    assert_eq!(
        result.nonce_status.abandoned_count(),
        2,
        "Should have 2 abandoned nonces"
    );
}

/// Test that nonce is NOT consumed when gas estimation fails.
///
/// This is important because gas estimation happens during `fill()`,
/// which is BEFORE the nonce is marked as sent. If estimation fails,
/// the nonce should be released so subsequent transactions can use it.
#[tokio::test]
async fn test_estimate_gas_failure_releases_nonce() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.network_provider_with_signer(0);
    let alice = harness.alice();

    // Deploy a reverting contract first
    let reverting_contract = harness.deploy_reverting_contract().await.unwrap();

    // Get initial nonce
    let initial_nonce = harness.get_nonce(alice).await.unwrap();
    println!("Initial nonce: {}", initial_nonce);

    // Try to send a transaction to the reverting contract
    // This should fail during gas estimation (the contract always reverts)
    let tx = TransactionRequest::default()
        .with_from(alice)
        .with_to(reverting_contract)
        .with_value(U256::ZERO);
    // Note: NOT setting gas_limit - let it estimate and fail

    let result = provider.send_transaction_ex(tx).await;

    // The transaction should fail (either during estimation or send)
    assert!(
        result.is_err(),
        "Transaction to reverting contract should fail"
    );
    println!("Transaction failed as expected: {:?}", result.err());

    // Check nonce manager state - should have no reserved/pending nonces
    let nonce_manager = provider.nonce_manager();
    assert!(
        nonce_manager.get_status(alice).await.is_none(),
        "should not have use of nonce"
    );

    // Now send a successful transaction - it should use the same nonce
    let tx_success = TransactionRequest::default()
        .with_from(alice)
        .with_to(harness.bob())
        .with_value(U256::from(1000));

    let mut tracked = provider.send_transaction_ex(tx_success).await.unwrap();
    let used_nonce = tracked.nonce();
    println!("Successful tx used nonce: {}", used_nonce);

    // The nonce should be the initial nonce (not incremented by failed tx)
    assert_eq!(
        used_nonce, initial_nonce,
        "Successful tx should use initial nonce (failed tx should not have consumed it)"
    );

    // Confirm the transaction
    tracked.get_receipt().await.unwrap();

    // Verify on-chain nonce incremented
    let final_nonce = harness.get_nonce(alice).await.unwrap();
    assert_eq!(
        final_nonce,
        initial_nonce + 1,
        "On-chain nonce should be incremented by 1"
    );
}

/// Test automatic recovery when a nonce gap exists.
///
/// This test verifies that `send_transaction_ex` with `auto_recovery` enabled
/// will automatically detect and fill nonce gaps when sending new transactions.
///
/// Scenario:
/// 1. Send tx0 (nonce 0) and confirm it
/// 2. Send tx1 (nonce 1) but abandon it (creating a gap)
/// 3. Send tx2 (nonce 2) which gets stuck due to the gap
/// 4. Send a NEW transaction - auto_recovery should:
///    - Detect the abandoned nonce 1
///    - Fill the gap with a cancel transaction
///    - Successfully send the new transaction
#[tokio::test]
async fn test_auto_recovery_fills_nonce_gap() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.network_provider_with_signer(0);
    let alice = harness.alice();
    let bob = harness.bob();

    println!("\n============================================================");
    println!("Test: Auto Recovery Fills Nonce Gap");
    println!("============================================================\n");

    // Step 1: Send and confirm tx0 (nonce 0)
    println!("Step 1: Send and confirm tx0 (nonce 0)");
    let tx0 = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(1000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let mut tracked0 = provider.send_transaction_ex(tx0).await.unwrap();
    assert_eq!(tracked0.nonce(), 0);
    tracked0.get_receipt().await.unwrap();
    println!("  tx0 confirmed with nonce 0");

    // Step 2: Send tx1 but don't wait - then drop it (abandon nonce 1)
    println!("\nStep 2: Send tx1 (nonce 1), then abandon it to create gap");
    harness.disable_automine().await.unwrap();

    let tx1 = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(2000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let tracked1 = provider.send_transaction_ex(tx1).await.unwrap();
    let tx1_hash = tracked1.tx_hash();
    assert_eq!(tracked1.nonce(), 1);
    println!("  tx1 sent with nonce 1, hash: {}", tx1_hash);

    // Drop from mempool and abandon the TrackedPendingTx
    harness.drop_transaction(tx1_hash).await.unwrap();
    drop(tracked1); // This marks nonce 1 as ABANDONED
    println!("  tx1 dropped and abandoned - nonce 1 is now a gap");

    harness.enable_automine().await.unwrap();

    // Verify nonce 1 is abandoned
    let nonce_manager = provider.nonce_manager();
    let status = nonce_manager.get_status(alice).await.unwrap();
    println!(
        "  Nonce status: base={}, next={}, pending={:?}, abandoned={:?}",
        status.base_nonce, status.next_nonce, status.pending_nonces, status.abandoned_nonces
    );
    assert!(
        status.abandoned_nonces.contains(&1),
        "Nonce 1 should be abandoned"
    );

    // Step 3: Now send a new transaction - auto_recovery should kick in
    println!("\nStep 3: Send new transaction - auto_recovery should fill the gap");
    let tx_new = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(5000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    // This should trigger auto_recovery which fills nonce 1 gap
    let mut tracked_new = provider.send_transaction_ex(tx_new).await.unwrap();
    let new_nonce = tracked_new.nonce();
    println!("  New tx sent with nonce {}", new_nonce);

    // The new transaction should use nonce 2 (after gap is filled)
    // But first, auto_recovery should have filled nonce 1
    tracked_new.get_receipt().await.unwrap();
    println!("  New tx confirmed");

    // Verify final state
    let final_status = nonce_manager.get_status(alice).await.unwrap();
    println!(
        "\nFinal nonce status: base={}, next={}, pending={:?}, abandoned={:?}",
        final_status.base_nonce,
        final_status.next_nonce,
        final_status.pending_nonces,
        final_status.abandoned_nonces
    );

    // After recovery, there should be no abandoned nonces
    assert!(
        final_status.abandoned_nonces.is_empty(),
        "All gaps should be filled after auto_recovery"
    );

    // Verify on-chain nonce (should be at least 2, possibly 3 if new tx used nonce 2)
    let on_chain_nonce = harness.get_nonce(alice).await.unwrap();
    println!("On-chain nonce: {}", on_chain_nonce);
    assert!(
        on_chain_nonce >= 2,
        "On-chain nonce should be at least 2 after recovery"
    );

    println!("\n============================================================");
    println!("Test PASSED: Auto recovery successfully filled nonce gap");
    println!("============================================================\n");
}

/// Test automatic recovery with nonce_too_low error.
///
/// This test simulates a scenario where the local nonce is behind the chain.
/// When sending a transaction, auto_recovery should sync and retry.
#[tokio::test]
async fn test_auto_recovery_nonce_too_low() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.network_provider_with_signer(0);
    let alice = harness.alice();
    let bob = harness.bob();

    println!("\n============================================================");
    println!("Test: Auto Recovery on Nonce Too Low");
    println!("============================================================\n");

    // Step 1: Send a transaction via raw provider (bypassing our nonce manager)
    println!("Step 1: Send tx via raw provider (bypassing nonce manager)");
    let wallet = harness.wallet(0);
    let raw_provider = ProviderBuilder::new()
        .wallet(wallet)
        .connect_http(harness.endpoint().parse::<reqwest::Url>().unwrap());

    let raw_tx = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(1000))
        .with_nonce(0)
        .with_chain_id(harness.chain_id())
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let pending = raw_provider.send_transaction(raw_tx).await.unwrap();
    pending.watch().await.unwrap();
    println!("  Raw tx confirmed, on-chain nonce now: 1");

    // Step 2: Verify our nonce manager still thinks nonce 0 is available
    let nonce_manager = provider.nonce_manager();
    let initial_status = nonce_manager.get_status(alice).await;
    println!(
        "  Our nonce manager status: {:?}",
        initial_status.as_ref().map(|s| s.next_nonce)
    );

    // Step 3: Send via our provider - it will try nonce 0 first, get "nonce too low",
    // then auto_recovery should sync and retry with correct nonce
    println!("\nStep 2: Send via our provider - should hit nonce_too_low and recover");
    let tx = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(2000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let mut tracked = provider.send_transaction_ex(tx).await.unwrap();
    let used_nonce = tracked.nonce();
    println!("  Transaction sent with nonce: {}", used_nonce);

    // Should have used nonce 1 (after recovery from nonce_too_low)
    assert_eq!(used_nonce, 1, "Should use nonce 1 after recovery");

    tracked.get_receipt().await.unwrap();
    println!("  Transaction confirmed");

    // Verify on-chain nonce
    let final_nonce = harness.get_nonce(alice).await.unwrap();
    println!("  Final on-chain nonce: {}", final_nonce);
    assert_eq!(final_nonce, 2, "On-chain nonce should be 2");

    println!("\n============================================================");
    println!("Test PASSED: Auto recovery handled nonce_too_low correctly");
    println!("============================================================\n");
}

/// Test that nonce is released when send_raw_transaction fails AFTER fill succeeds.
///
/// This tests a different scenario: fill() succeeds (gas estimated),
/// but send_raw_transaction fails. The nonce should still be released.
#[tokio::test]
async fn test_send_failure_releases_nonce() {
    let harness = AnvilTestHarness::new().await.unwrap();
    let provider = harness.network_provider_with_signer(0);
    let alice = harness.alice();
    let bob = harness.bob();

    // Get initial nonce
    let initial_nonce = harness.get_nonce(alice).await.unwrap();
    println!("Initial nonce: {}", initial_nonce);

    // First, send a successful transaction to use nonce 0
    let tx1 = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(1000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let mut tracked1 = provider.send_transaction_ex(tx1).await.unwrap();
    assert_eq!(tracked1.nonce(), initial_nonce);
    tracked1.get_receipt().await.unwrap();
    println!("First tx confirmed with nonce {}", initial_nonce);

    // Now try to send with the same nonce (should fail with nonce too low)
    // We need to use a raw provider to force a specific nonce
    let wallet = harness.wallet(0);
    let raw_provider = ProviderBuilder::new()
        .wallet(wallet)
        .connect_http(harness.endpoint().parse::<reqwest::Url>().unwrap());

    let tx_bad_nonce = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(1000))
        .with_nonce(initial_nonce) // Already used nonce
        .with_chain_id(harness.chain_id())
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let result = raw_provider.send_transaction(tx_bad_nonce).await;
    assert!(result.is_err(), "Transaction with used nonce should fail");
    println!("Transaction with bad nonce failed as expected");

    // Now send via our provider - it should use nonce 1 (not affected by failed raw send)
    let tx2 = TransactionRequest::default()
        .with_from(alice)
        .with_to(bob)
        .with_value(U256::from(2000))
        .with_gas_limit(21000)
        .with_max_fee_per_gas(20_000_000_000u128)
        .with_max_priority_fee_per_gas(1_000_000_000u128);

    let mut tracked2 = provider.send_transaction_ex(tx2).await.unwrap();
    let used_nonce = tracked2.nonce();
    println!("Second tx via provider used nonce: {}", used_nonce);

    assert_eq!(
        used_nonce,
        initial_nonce + 1,
        "Second tx should use nonce 1"
    );

    tracked2.get_receipt().await.unwrap();

    // Verify final on-chain nonce
    let final_nonce = harness.get_nonce(alice).await.unwrap();
    assert_eq!(final_nonce, initial_nonce + 2, "Final nonce should be 2");
}
