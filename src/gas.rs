//! Gas pricing utilities for transaction replacement.
//!
//! This module provides `TxGas` for extracting and applying gas pricing
//! to replacement transactions (cancel TX, gap filling).

use alloy::{
    consensus::Transaction,
    network::{Ethereum, Network},
    primitives::{Address, U256},
    providers::Provider,
    rpc::types::TransactionRequest,
    transports::TransportResult,
};

/// Gas pricing source for replacement transactions.
///
/// Used by cancel TX and gap filling to determine how to price the replacement.
#[derive(Debug, Clone, Copy)]
pub enum TxGas {
    /// EIP-1559 gas pricing
    Eip1559 { max_fee: u128, max_priority_fee: u128 },
    /// Legacy gas pricing
    Legacy { gas_price: u128 },
    /// Estimate gas fees from the network
    FromNetwork,
}

impl TxGas {
    /// Extract gas pricing from a transaction envelope.
    pub fn from_envelope<N: Network>(envelope: &N::TxEnvelope) -> Self {
        if let Some(max_priority_fee) = envelope.max_priority_fee_per_gas() {
            TxGas::Eip1559 {
                max_fee: envelope.max_fee_per_gas(),
                max_priority_fee,
            }
        } else if let Some(gas_price) = envelope.gas_price() {
            TxGas::Legacy { gas_price }
        } else {
            TxGas::FromNetwork
        }
    }

    /// Build a replacement transaction (0 ETH to self) with gas pricing applied.
    ///
    /// This is commonly used for:
    /// - Cancel transactions (replacing a pending TX with a no-op)
    /// - Gap filling (filling abandoned nonce slots)
    ///
    /// ## Parameters
    /// - `from`: The sender address (TX will be sent to self)
    /// - `nonce`: The nonce to use
    /// - `provider`: Provider for fetching network gas prices
    /// - `multiplier`: Gas price multiplier (e.g., 1.1 for 10% boost)
    pub async fn build_replacement_tx<P: Provider<Ethereum>>(
        self,
        from: Address,
        nonce: u64,
        provider: &P,
        multiplier: f64,
    ) -> TransportResult<TransactionRequest> {
        let mut tx = TransactionRequest::default()
            .from(from)
            .to(from)
            .value(U256::ZERO)
            .nonce(nonce);

        self.apply_to_tx(&mut tx, provider, multiplier).await?;

        Ok(tx)
    }

    /// Apply gas pricing to a transaction request with the given multiplier.
    ///
    /// Uses the same transaction type as the original:
    /// - `Eip1559` → fetches network EIP-1559 fees, uses `max(boosted_original, network)`
    /// - `Legacy` → fetches network gas price, uses `max(boosted_original, network)`
    /// - `FromNetwork` → auto-detects (tries EIP-1559 first, falls back to legacy)
    pub async fn apply_to_tx<P: Provider<Ethereum>>(
        self,
        tx: &mut TransactionRequest,
        provider: &P,
        multiplier: f64,
    ) -> TransportResult<()> {
        match self {
            TxGas::Eip1559 { max_fee, max_priority_fee } => {
                let boosted_max_fee = (max_fee as f64 * multiplier) as u128;
                let boosted_priority_fee = (max_priority_fee as f64 * multiplier) as u128;

                // Fetch network EIP-1559 fees and use max
                let (final_max_fee, final_priority_fee) =
                    match provider.estimate_eip1559_fees().await {
                        Ok(fees) => (
                            boosted_max_fee.max(fees.max_fee_per_gas),
                            boosted_priority_fee.max(fees.max_priority_fee_per_gas),
                        ),
                        Err(_) => (boosted_max_fee, boosted_priority_fee),
                    };

                *tx = std::mem::take(tx)
                    .max_fee_per_gas(final_max_fee)
                    .max_priority_fee_per_gas(final_priority_fee);

                tracing::debug!(
                    original_max_fee = max_fee,
                    boosted_max_fee,
                    final_max_fee,
                    final_priority_fee,
                    multiplier,
                    "applied EIP-1559 gas"
                );
            }

            TxGas::Legacy { gas_price } => {
                let boosted_gas_price = (gas_price as f64 * multiplier) as u128;

                // Fetch network gas price and use max
                let final_gas_price = match provider.get_gas_price().await {
                    Ok(net_gas) => boosted_gas_price.max(net_gas),
                    Err(_) => boosted_gas_price,
                };

                *tx = std::mem::take(tx).gas_price(final_gas_price);

                tracing::debug!(
                    original_gas_price = gas_price,
                    boosted_gas_price,
                    final_gas_price,
                    multiplier,
                    "applied legacy gas"
                );
            }

            TxGas::FromNetwork => {
                // Auto-detect: try EIP-1559 first, fall back to legacy
                if let Ok(fees) = provider.estimate_eip1559_fees().await {
                    let boosted_max_fee = (fees.max_fee_per_gas as f64 * multiplier) as u128;
                    let boosted_priority_fee =
                        (fees.max_priority_fee_per_gas as f64 * multiplier) as u128;

                    *tx = std::mem::take(tx)
                        .max_fee_per_gas(boosted_max_fee)
                        .max_priority_fee_per_gas(boosted_priority_fee);

                    tracing::debug!(
                        network_max_fee = fees.max_fee_per_gas,
                        boosted_max_fee,
                        boosted_priority_fee,
                        multiplier,
                        "applied EIP-1559 gas from network"
                    );
                } else {
                    let gas_price = provider.get_gas_price().await?;
                    let boosted_gas_price = (gas_price as f64 * multiplier) as u128;

                    *tx = std::mem::take(tx).gas_price(boosted_gas_price);

                    tracing::debug!(
                        network_gas_price = gas_price,
                        boosted_gas_price,
                        multiplier,
                        "applied legacy gas from network"
                    );
                }
            }
        }
        Ok(())
    }
}
