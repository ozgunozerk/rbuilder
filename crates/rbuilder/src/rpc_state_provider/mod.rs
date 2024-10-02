/// Instead of having the full `State`,
/// we fetch the necessary information from the `Reth RPC`,
///
/// implements `Database` trait required by `EvmBuilder::with_db`
use std::str::FromStr;

use ahash::HashMap;
use alloy_primitives::{
    hex, keccak256, Address as AlloyAddress, Bytes as AlloyBytes, B256 as AlloyB256,
    U256 as AlloyU256,
};
use ethers::types::{Address as EthersAddress, H256 as EthersH256, U256 as EthersU256}; // Ether's types
use ethers::{
    middleware::Middleware,
    providers::{Http, JsonRpcClient, Provider},
};
use futures::executor::block_on;
use revm::primitives::KECCAK_EMPTY;
use revm_primitives::{AccountInfo, Bytecode};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum RPCError {
    #[error("RPC call failed: {0} at method {1}")]
    RpcCallError(String, String),
    #[error("RPC construction failed: {0}")]
    RpcConstructionError(String),
    #[error("Code could not found for hash: {0}")]
    CodeNotFound(String),
}

#[derive(Debug)]
pub struct RPCDatabase<P> {
    provider: Provider<P>, // Ethers provider for RPC calls
    cache: RpcCache,
}

#[derive(Debug, Default)]
pub struct RpcCache {
    block_hashes: HashMap<u64, AlloyB256>,
    balances: HashMap<AlloyAddress, AlloyU256>,
    nonces: HashMap<AlloyAddress, u64>,
    codes: HashMap<AlloyAddress, AlloyBytes>,
    code_hashes: HashMap<AlloyB256, AlloyBytes>,
    storages: HashMap<AlloyAddress, AlloyU256>,
}

impl RPCDatabase<Http> {
    pub fn new(provider_url: &str) -> Result<Self, RPCError> {
        let provider = Provider::<Http>::try_from(provider_url)
            .map_err(|e| RPCError::RpcConstructionError(e.to_string()))?;

        let cache = RpcCache::default();

        Ok(Self { provider, cache })
    }
}

impl<P> RPCDatabase<P>
where
    P: JsonRpcClient,
{
    pub fn from_provider(provider: Provider<P>) -> Self {
        let cache = RpcCache::default();

        Self { provider, cache }
    }

    async fn get_balance(&mut self, address: AlloyAddress) -> Result<AlloyU256, RPCError> {
        let cached_balance = self.cache.balances.get(&address);
        if let Some(&balance) = cached_balance {
            return Ok(balance);
        }

        let balance = self
            .provider
            .get_balance(Self::from_alloy_to_ethers_address(address), None)
            .await
            .map(|balance| AlloyU256::from(balance.as_u64()))
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_balance".to_string()))?;

        // Update the cache
        self.cache.balances.insert(address, balance);

        Ok(balance)
    }

    async fn get_nonce(&mut self, address: AlloyAddress) -> Result<u64, RPCError> {
        let cached_nonce = self.cache.nonces.get(&address);
        if let Some(&nonce) = cached_nonce {
            return Ok(nonce);
        }

        let nonce = self
            .provider
            .get_transaction_count(Self::from_alloy_to_ethers_address(address), None)
            .await
            .map(|nonce| nonce.as_u64())
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_nonce".to_string()))?;

        self.cache.nonces.insert(address, nonce);

        Ok(nonce)
    }

    async fn get_code(&mut self, address: AlloyAddress) -> Result<AlloyBytes, RPCError> {
        let cached_code = self.cache.codes.get(&address);
        if let Some(code) = cached_code {
            return Ok(code.clone());
        }

        let code = self
            .provider
            .get_code(Self::from_alloy_to_ethers_address(address), None)
            .await
            .map(|bytes| {
                let bytes_vec: Vec<u8> = bytes.to_vec();
                AlloyBytes::from(bytes_vec)
            })
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_code".to_string()))?;

        self.cache.codes.insert(address, code.clone());

        // Also update the code_hashes cache
        let code_hash = hex::encode(keccak256(&code));
        let code_hash = AlloyB256::from_str(&code_hash).unwrap();
        self.cache.code_hashes.insert(code_hash, code.clone());

        Ok(code)
    }

    // Helper function to fetch storage
    async fn get_storage(
        &mut self,
        address: AlloyAddress,
        index: AlloyU256,
    ) -> Result<AlloyU256, RPCError> {
        let index_u256 = Self::from_alloy_to_ethers_u256(index);
        let index = Self::from_ethers_u256_to_ethers_h256(index_u256);

        let cached_storage = self.cache.storages.get(&address);
        if let Some(&storage) = cached_storage {
            return Ok(storage);
        }

        let storage = self
            .provider
            .get_storage_at(Self::from_alloy_to_ethers_address(address), index, None)
            .await
            .map(|h256| {
                let storage = Self::from_ether_to_alloy_h256(h256);
                Self::from_alloy_b256_to_alloy_u256(storage)
            })
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_storage".to_string()))?;

        self.cache.storages.insert(address, storage);

        Ok(storage)
    }

    // Helper function to fetch block hash
    async fn get_block_hash(&mut self, block_number: u64) -> Result<AlloyB256, RPCError> {
        let cached_block_hash = self.cache.block_hashes.get(&block_number);
        if let Some(&block_hash) = cached_block_hash {
            return Ok(block_hash);
        }

        let block_hash = self
            .provider
            .get_block(block_number as u64)
            .await
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_block_hash".to_string()))
            .map(|block| {
                let block_hash = block.unwrap().hash.unwrap();
                Self::from_ether_to_alloy_h256(block_hash)
            })?;

        self.cache.block_hashes.insert(block_number, block_hash);

        Ok(block_hash)
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
impl<P> revm::Database for RPCDatabase<P>
where
    P: JsonRpcClient,
{
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
            Err(_) => (None, KECCAK_EMPTY),
        };

        let account_info = AccountInfo {
            nonce,
            balance,
            code,
            code_hash, // Placeholder for actual code hash
        };
        Ok(Some(account_info))
    }

    fn code_by_hash(&mut self, code_hash: AlloyB256) -> Result<Bytecode, Self::Error> {
        self.cache
            .code_hashes
            .get(&code_hash)
            .cloned()
            .map(|bytes| Bytecode::LegacyRaw(bytes.into()))
            .ok_or(RPCError::CodeNotFound(code_hash.to_string()))
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

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::hex::decode;
    use ethers::{
        providers::MockProvider,
        types::{Block, Bytes},
    };
    use revm::Database;

    #[tokio::test]
    async fn mock_rpc_get_balance() {
        let (provider, mock) = Provider::mocked();
        let mut rpc_db = RPCDatabase::from_provider(provider);
        let address = AlloyAddress::from_str("0x1234567890123456789012345678901234567890").unwrap();

        mock.push(EthersU256::from(1000u64)).unwrap();

        let balance = rpc_db.get_balance(address).await.unwrap();
        assert_eq!(balance, AlloyU256::from(1000u64));
    }

    #[tokio::test]
    async fn mock_rpc_get_nonce() {
        let (provider, mock) = Provider::mocked();
        let mut rpc_db = RPCDatabase::from_provider(provider);
        let address = AlloyAddress::from_str("0x1234567890123456789012345678901234567890").unwrap();

        mock.push(EthersU256::from(5u64)).unwrap();

        let nonce = rpc_db.get_nonce(address).await.unwrap();
        assert_eq!(nonce, 5);
    }

    #[tokio::test]
    async fn mock_rpc_get_code() {
        let (provider, mock) = Provider::mocked();
        let mut rpc_db = RPCDatabase::from_provider(provider);
        let address = AlloyAddress::from_str("0x1234567890123456789012345678901234567890").unwrap();
        let code_hex = "6001600101"; // Example bytecode in hex
        let code_bytes = decode(code_hex).expect("Invalid hex string"); // Convert hex string to Vec<u8>
        let code = Bytes::from(code_bytes.clone());

        // Push the serialized bytes to the mock
        mock.push::<Bytes, _>(code).unwrap();

        let fetched_code = rpc_db.get_code(address).await.unwrap();
        assert_eq!(fetched_code, AlloyBytes::from(code_bytes.to_vec()));
    }

    #[tokio::test]
    async fn mock_rpc_get_storage() {
        let (provider, mock) = Provider::mocked();
        let mut rpc_db = RPCDatabase::from_provider(provider);
        let address = AlloyAddress::from_str("0x1234567890123456789012345678901234567890").unwrap();
        let storage_index = AlloyU256::from(1u64);
        let storage_value = EthersH256::from_low_u64_be(42);

        mock.push(storage_value).unwrap();

        let fetched_storage = rpc_db.get_storage(address, storage_index).await.unwrap();
        assert_eq!(fetched_storage, AlloyU256::from(42u64));
    }

    #[tokio::test]
    async fn mock_rpc_get_block_hash() {
        let (provider, mock) = Provider::mocked();
        let mut rpc_db = RPCDatabase::from_provider(provider);
        let block_number = 12345;
        let block_hash = EthersH256::from_low_u64_be(0xabcdef);

        // Create a mock Block object
        let block: Block<EthersH256> = Block {
            hash: Some(block_hash), // This should be of type EthersH256 or whatever your Block struct expects
            number: Some(block_number.into()), // Add any other required fields for your Block
            ..Default::default()    // Ensure other required fields are filled out as needed
        };

        // Push the mock Block into the provider
        mock.push(block).unwrap();

        let fetched_block_hash = rpc_db.get_block_hash(block_number).await.unwrap();
        assert_eq!(
            fetched_block_hash,
            RPCDatabase::<MockProvider>::from_ether_to_alloy_h256(block_hash)
        );
    }

    #[test]
    fn integration_test_rpc_database() {
        // Setup: Create a mocked provider and an RPCDatabase instance
        let (provider, mock) = Provider::mocked();
        let mut rpc_db = RPCDatabase::from_provider(provider);

        // // Define test parameters
        let test_address =
            AlloyAddress::from_str("0x1234567890123456789012345678901234567890").unwrap();
        let block_number = 12345;
        let block_hash = EthersH256::from_low_u64_be(0xabcdef);
        let test_balance = AlloyU256::from(1000);
        let test_nonce = 42;
        let code_hex = "6001600101"; // Example bytecode in hex
        let code_bytes = decode(code_hex).expect("Invalid hex string"); // Convert hex string to Vec<u8>
        let test_code = Bytes::from(code_bytes.clone());

        // Create a mock Block object for block hash
        let test_block: Block<EthersH256> = Block {
            hash: Some(block_hash),
            number: Some(block_number.into()),
            ..Default::default()
        };
        mock.push(test_block).unwrap();

        mock.push::<Bytes, _>(test_code).unwrap();
        mock.push(EthersU256::from(test_nonce)).unwrap();
        mock.push(test_balance).unwrap();

        // Act: Call the methods from the Database trait
        let fetched_account_info = rpc_db.basic(test_address).unwrap().unwrap();
        let fetched_balance = fetched_account_info.balance;
        let fetched_nonce = fetched_account_info.nonce;

        let fetched_block_hash = rpc_db.block_hash(block_number).unwrap();

        // Assert: Verify the results
        assert_eq!(fetched_account_info.nonce, test_nonce as u64);
        assert_eq!(fetched_balance, test_balance);
        assert_eq!(
            fetched_block_hash,
            RPCDatabase::<MockProvider>::from_ether_to_alloy_h256(block_hash)
        );
        assert_eq!(fetched_nonce, test_nonce);
    }
}
