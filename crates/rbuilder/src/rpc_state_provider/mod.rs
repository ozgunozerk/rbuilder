use std::str::FromStr;

use alloy_primitives::{
    hex, keccak256, Address as AlloyAddress, Bytes as AlloyBytes, B256 as AlloyB256,
    U256 as AlloyU256,
};
/// Instead of having the full `State`,
/// we fetch the necessary information from the `Reth RPC`,
///
/// implements `Database` trait required by `EvmBuilder::with_db`
use ethers::prelude::*; // for making RPC calls
use ethers::types::{Address as EthersAddress, H256 as EthersH256, U256 as EthersU256}; // Ether's types
use futures::executor::block_on;
use revm_primitives::{AccountInfo, Bytecode};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum RPCError {
    #[error("RPC call failed: {0}")]
    RpcCallError(String),
    #[error("RPC construction failedd: {0}")]
    RpcConstructionError(String),
    #[error("code_by_hash method makes no sense in RPC state provider")]
    UnsupportedOperation,
}

pub struct RPCDatabase {
    provider: Provider<Http>, // Ethers provider for RPC calls
}

impl RPCDatabase {
    pub fn new(provider_url: &str) -> Result<Self, RPCError> {
        let provider = Provider::<Http>::try_from(provider_url)
            .map_err(|e| RPCError::RpcConstructionError(e.to_string()))?;
        Ok(Self { provider })
    }

    // Helper function to fetch balance
    async fn get_balance(&self, address: AlloyAddress) -> Result<AlloyU256, RPCError> {
        self.provider
            .get_balance(Self::from_alloy_to_ethers_address(address), None)
            .await
            .map(|balance| AlloyU256::from(balance.as_u64()))
            .map_err(|e| RPCError::RpcCallError(e.to_string()))
    }

    // Helper function to fetch nonce
    async fn get_nonce(&self, address: AlloyAddress) -> Result<u64, RPCError> {
        self.provider
            .get_transaction_count(Self::from_alloy_to_ethers_address(address), None)
            .await
            .map(|nonce| nonce.as_u64())
            .map_err(|e| RPCError::RpcCallError(e.to_string()))
    }

    // Helper function to fetch code
    async fn get_code(&self, address: AlloyAddress) -> Result<AlloyBytes, RPCError> {
        self.provider
            .get_code(Self::from_alloy_to_ethers_address(address), None)
            .await
            .map(|bytes| {
                let bytes_vec: Vec<u8> = bytes.to_vec();
                AlloyBytes::from(bytes_vec)
            })
            .map_err(|e| RPCError::RpcCallError(e.to_string()))
    }

    // Helper function to fetch storage
    async fn get_storage(
        &self,
        address: AlloyAddress,
        index: AlloyU256,
    ) -> Result<AlloyU256, RPCError> {
        let index_u256 = Self::from_alloy_to_ethers_u256(index);
        let index = Self::from_ethers_u256_to_ethers_h256(index_u256);
        self.provider
            .get_storage_at(Self::from_alloy_to_ethers_address(address), index, None)
            .await
            .map(|h256| {
                let storage = Self::from_ether_to_alloy_h256(h256);
                Self::from_alloy_b256_to_alloy_u256(storage)
            })
            .map_err(|e| RPCError::RpcCallError(e.to_string()))
    }

    // Helper function to fetch block hash
    async fn get_block_hash(&self, block_number: u64) -> Result<AlloyB256, RPCError> {
        self.provider
            .get_block(block_number)
            .await
            .map_err(|e| RPCError::RpcCallError(e.to_string()))
            .map(|block| {
                let block_hash = block.unwrap().hash.unwrap();
                Self::from_ether_to_alloy_h256(block_hash)
            })
    }

    fn from_alloy_to_ethers_address(address: AlloyAddress) -> EthersAddress {
        EthersAddress::from_slice(address.as_slice())
    }

    fn from_alloy_to_ethers_u256(hash: AlloyU256) -> EthersU256 {
        let bytes: [u8; 32] = hash.to_be_bytes();
        EthersU256::from_big_endian(&bytes)
    }

    fn from_ether_to_alloy_h256(hash: EthersH256) -> AlloyB256 {
        AlloyB256::from_slice(hash.0.as_slice())
    }

    fn from_alloy_b256_to_alloy_u256(hash: AlloyB256) -> AlloyU256 {
        let bytes: [u8; 32] = hash.0.as_slice().try_into().unwrap();
        AlloyU256::from_be_bytes(bytes)
    }

    fn from_ethers_u256_to_ethers_h256(hash: EthersU256) -> EthersH256 {
        let mut bytes = [0u8; 32];
        hash.to_big_endian(&mut bytes);
        EthersH256::from_slice(&bytes)
    }
}

// Blocking implementation of Database trait for revm
impl revm::Database for RPCDatabase {
    type Error = RPCError;

    fn basic(&mut self, address: AlloyAddress) -> Result<Option<AccountInfo>, Self::Error> {
        // Fetch balance, nonce, and code in a blocking manner
        let balance = block_on(self.get_balance(address))?;
        let nonce = block_on(self.get_nonce(address))?;
        let (code, code_hash) = match block_on(self.get_code(address)) {
            Ok(code) => {
                let code_hash = hex::encode(keccak256(&code));
                let code_hash = AlloyB256::from_str(&code_hash).unwrap();

                (Some(Bytecode::new_raw(code)), code_hash)
            } // TODO: hash the code
            Err(_) => (None, AlloyB256::default()),
        };

        let account_info = AccountInfo {
            nonce,
            balance,
            code,
            code_hash, // Placeholder for actual code hash
        };
        Ok(Some(account_info))
    }

    fn code_by_hash(&mut self, _code_hash: AlloyB256) -> Result<Bytecode, Self::Error> {
        // Use the code hash to fetch the code from the blockchain
        Err(RPCError::UnsupportedOperation)
    }

    fn storage(
        &mut self,
        address: AlloyAddress,
        index: AlloyU256,
    ) -> Result<AlloyU256, Self::Error> {
        // Fetch storage value at index for the provided address
        block_on(self.get_storage(address, index))
    }

    fn block_hash(&mut self, number: u64) -> Result<AlloyB256, Self::Error> {
        // Fetch the block hash for a given block number
        block_on(self.get_block_hash(number))
    }
}
