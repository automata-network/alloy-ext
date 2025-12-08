//! Nonce behavior test scenario framework.
//!
//! This module provides `NonceBehaviorScenario` for testing nonce management
//! behavior in various scenarios like confirmations, abandonments, and gaps.

use std::sync::Arc;

use alloy::{
    network::{Ethereum, TransactionBuilder},
    primitives::{B256, U256},
    rpc::types::TransactionRequest,
};
use anyhow::{anyhow, Result};

use crate::ext::{
    nonce_state, AtomicNonceState, NetworkProvider, NonceStatus, ProviderEx, TrackedPendingTx,
};

use super::AnvilTestHarness;

// ============================================================================
// TxAction
// ============================================================================

/// What action to take on a transaction during the test
#[derive(Debug, Clone, PartialEq)]
pub enum TxAction {
    /// Call get_receipt() to confirm the transaction
    Confirm,
    /// Drop from mempool + drop TrackedPendingTx (marks nonce as abandoned)
    DropAndAbandon,
    /// Leave the transaction pending (don't call get_receipt or drop)
    LeaveStuck,
}

// ============================================================================
// ExpectedNonceState
// ============================================================================

/// Expected final state of a nonce
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedNonceState {
    /// Nonce should be confirmed (transaction mined)
    Confirmed,
    /// Nonce should be abandoned (needs gap filling)
    Abandoned,
    /// Nonce should still be pending (stuck due to gap or not yet processed)
    Pending,
}

impl ExpectedNonceState {
    pub(crate) fn matches(&self, state: u8) -> bool {
        match self {
            ExpectedNonceState::Confirmed => state == nonce_state::CONFIRMED,
            ExpectedNonceState::Abandoned => state == nonce_state::ABANDONED,
            ExpectedNonceState::Pending => state == nonce_state::PENDING,
        }
    }

    pub(crate) fn state_name(&self) -> &'static str {
        match self {
            ExpectedNonceState::Confirmed => "CONFIRMED",
            ExpectedNonceState::Abandoned => "ABANDONED",
            ExpectedNonceState::Pending => "PENDING",
        }
    }
}

// ============================================================================
// TxSpec
// ============================================================================

/// Specification for a single transaction in a test scenario
#[derive(Debug, Clone)]
pub struct TxSpec {
    /// Human-readable name for this transaction
    pub name: String,
    /// Action to take on this transaction
    pub action: TxAction,
    /// Expected final state of the nonce
    pub expected_state: ExpectedNonceState,
}

impl TxSpec {
    pub fn new(name: impl Into<String>, action: TxAction, expected: ExpectedNonceState) -> Self {
        Self {
            name: name.into(),
            action,
            expected_state: expected,
        }
    }

    /// Create a transaction that will be confirmed
    pub fn confirm(name: impl Into<String>) -> Self {
        Self::new(name, TxAction::Confirm, ExpectedNonceState::Confirmed)
    }

    /// Create a transaction that will be dropped from mempool and abandoned
    pub fn drop_and_abandon(name: impl Into<String>) -> Self {
        Self::new(
            name,
            TxAction::DropAndAbandon,
            ExpectedNonceState::Abandoned,
        )
    }

    /// Create a transaction that will be left stuck (pending but blocked)
    pub fn leave_stuck(name: impl Into<String>) -> Self {
        Self::new(name, TxAction::LeaveStuck, ExpectedNonceState::Pending)
    }
}

// ============================================================================
// TxRuntime
// ============================================================================

/// Runtime state for a transaction during test execution
struct TxRuntime {
    spec: TxSpec,
    nonce: u64,
    tx_hash: B256,
    tracked: Option<TrackedPendingTx<NetworkProvider, Ethereum>>,
    atomic_state: Arc<AtomicNonceState>,
}

// ============================================================================
// NonceBehaviorScenario
// ============================================================================

/// A configurable test scenario for nonce behavior
///
/// # Example
///
/// ```ignore
/// NonceBehaviorScenario::new("Gap in middle")
///     .description("Tests what happens when middle tx is abandoned")
///     .tx(TxSpec::confirm("tx0"))
///     .tx(TxSpec::drop_and_abandon("tx1"))
///     .tx(TxSpec::leave_stuck("tx2"))
///     .run(&harness)
///     .await
///     .unwrap();
/// ```
pub struct NonceBehaviorScenario {
    name: String,
    description: Option<String>,
    tx_specs: Vec<TxSpec>,
}

impl NonceBehaviorScenario {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: None,
            tx_specs: Vec::new(),
        }
    }

    pub fn description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }

    pub fn tx(mut self, spec: TxSpec) -> Self {
        self.tx_specs.push(spec);
        self
    }

    /// Run the scenario and verify results
    pub async fn run(self, harness: &AnvilTestHarness) -> Result<ScenarioResult> {
        println!("\n{}", "=".repeat(60));
        println!("Scenario: {}", self.name);
        if let Some(desc) = &self.description {
            println!("Description: {}", desc);
        }
        println!("{}\n", "=".repeat(60));

        let provider = harness.network_provider_with_signer(0);
        let alice = harness.alice();
        let bob = harness.bob();

        // Phase 1: Disable automine and send all transactions
        println!("Phase 1: Sending {} transactions...", self.tx_specs.len());
        harness.disable_automine().await?;

        let mut runtimes: Vec<TxRuntime> = Vec::new();

        for (i, spec) in self.tx_specs.into_iter().enumerate() {
            let tx = TransactionRequest::default()
                .with_from(alice)
                .with_to(bob)
                .with_value(U256::from(1000 + i as u64))
                .with_gas_limit(21000)
                .with_max_fee_per_gas(20_000_000_000u128)
                .with_max_priority_fee_per_gas(1_000_000_000u128);

            let tracked = provider.send_transaction_ex(tx).await?;
            let nonce = tracked.nonce();
            let tx_hash = tracked.tx_hash();
            let atomic_state = tracked.atomic_state().clone();

            println!(
                "  [{}] '{}' sent with nonce {} (action: {:?})",
                i, spec.name, nonce, spec.action
            );

            runtimes.push(TxRuntime {
                spec,
                nonce,
                tx_hash,
                tracked: Some(tracked),
                atomic_state,
            });
        }

        // Phase 2: Execute actions that need to happen before mining
        println!("\nPhase 2: Executing pre-mine actions...");
        for runtime in &mut runtimes {
            if let TxAction::DropAndAbandon = &runtime.spec.action {
                // Drop from mempool first
                harness.drop_transaction(runtime.tx_hash).await?;
                println!(
                    "  [{}] '{}' dropped from mempool",
                    runtime.nonce, runtime.spec.name
                );
                // Then drop the TrackedPendingTx
                runtime.tracked.take();
                println!(
                    "  [{}] '{}' TrackedPendingTx dropped -> ABANDONED",
                    runtime.nonce, runtime.spec.name
                );
            }
        }

        // Phase 3: Enable automine and mine a block
        println!("\nPhase 3: Mining...");
        harness.enable_automine().await?;
        harness.mine_block().await?;
        println!("  Block mined");

        // Phase 4: Execute post-mine actions (confirmations)
        println!("\nPhase 4: Executing post-mine actions...");
        for runtime in &mut runtimes {
            if let TxAction::Confirm = runtime.spec.action {
                if let Some(tracked) = &mut runtime.tracked {
                    match tracked.get_receipt().await {
                        Ok(_) => {
                            println!(
                                "  [{}] '{}' get_receipt() succeeded -> CONFIRMED",
                                runtime.nonce, runtime.spec.name
                            );
                        }
                        Err(e) => {
                            println!(
                                "  [{}] '{}' get_receipt() failed: {} (may be stuck)",
                                runtime.nonce, runtime.spec.name, e
                            );
                        }
                    }
                }
            }
        }

        // Phase 5: Verify results
        println!("\nPhase 5: Verifying results...");
        let mut all_passed = true;
        let mut results = Vec::new();

        for runtime in &runtimes {
            let actual_state = runtime.atomic_state.get();
            let expected = &runtime.spec.expected_state;
            let passed = expected.matches(actual_state);

            let actual_name = match actual_state {
                nonce_state::RESERVED => "RESERVED",
                nonce_state::PENDING => "PENDING",
                nonce_state::ABANDONED => "ABANDONED",
                nonce_state::CONFIRMED => "CONFIRMED",
                _ => "UNKNOWN",
            };

            let status = if passed { "PASS" } else { "FAIL" };
            println!(
                "  {} [{}] '{}': expected {}, got {}",
                status,
                runtime.nonce,
                runtime.spec.name,
                expected.state_name(),
                actual_name
            );

            if !passed {
                all_passed = false;
            }

            results.push(TxResult {
                name: runtime.spec.name.clone(),
                nonce: runtime.nonce,
                expected_state: runtime.spec.expected_state,
                actual_state,
                passed,
            });
        }

        // Phase 6: Check nonce manager status
        println!("\nPhase 6: Nonce manager status...");
        let nonce_manager = provider.nonce_manager();
        let status = nonce_manager
            .get_status(alice)
            .await
            .ok_or_else(|| anyhow!("Failed to get nonce status for {}", alice))?;
        println!(
            "  base_nonce={}, next_nonce={}, pending={:?}, abandoned={:?}",
            status.base_nonce, status.next_nonce, status.pending_nonces, status.abandoned_nonces
        );

        println!("\n{}", "=".repeat(60));
        if all_passed {
            println!("Result: ALL PASSED");
        } else {
            println!("Result: SOME FAILED");
        }
        println!("{}\n", "=".repeat(60));

        Ok(ScenarioResult {
            name: self.name,
            all_passed,
            tx_results: results,
            nonce_status: status,
        })
    }
}

// ============================================================================
// TxResult
// ============================================================================

/// Result of a single transaction in a scenario
#[derive(Debug)]
pub struct TxResult {
    pub name: String,
    pub nonce: u64,
    pub expected_state: ExpectedNonceState,
    pub actual_state: u8,
    pub passed: bool,
}

// ============================================================================
// ScenarioResult
// ============================================================================

/// Result of running a scenario
#[derive(Debug)]
pub struct ScenarioResult {
    pub name: String,
    pub all_passed: bool,
    pub tx_results: Vec<TxResult>,
    pub nonce_status: NonceStatus,
}

impl ScenarioResult {
    pub fn assert_passed(&self) {
        assert!(
            self.all_passed,
            "Scenario '{}' failed: {:?}",
            self.name,
            self.tx_results
                .iter()
                .filter(|r| !r.passed)
                .collect::<Vec<_>>()
        );
    }
}
