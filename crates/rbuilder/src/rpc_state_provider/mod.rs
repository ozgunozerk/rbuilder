/// Instead of having the full `State`,
/// we fetch the necessary information from the `Reth RPC`,
///
/// implements `Database` trait required by `EvmBuilder::with_db`
use std::str::FromStr;

use ahash::HashMap;
use alloy_primitives::{hex, keccak256, Address, Bytes, B256, U256};
use alloy_provider::{Provider, ProviderBuilder, RootProvider};
use alloy_transport::Transport;
use alloy_transport_http::Client;
// use ethers::types::{Address as EthersAddress, H256 as EthersH256, U256 as EthersU256}; // Ether's types
// use ethers::{
//     middleware::Middleware,
//     providers::{Http, JsonRpcClient, Provider},
// };
use alloy_transport_http::Http;
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
    provider: RootProvider<P>, // Ethers provider for RPC calls
    cache: RpcCache,
}

#[derive(Debug, Default)]
pub struct RpcCache {
    block_hashes: HashMap<u64, B256>,
    balances: HashMap<Address, U256>,
    nonces: HashMap<Address, u64>,
    codes: HashMap<Address, Bytes>,
    code_hashes: HashMap<B256, Bytes>,
    storages: HashMap<Address, U256>,
}

impl RPCDatabase<Http<Client>> {
    pub fn new(provider_url: &str) -> Result<Self, RPCError> {
        let url = url::Url::parse(provider_url)
            .map_err(|e| RPCError::RpcConstructionError(e.to_string()))?;
        let provider = ProviderBuilder::new().on_http(url);

        let cache = RpcCache::default();

        Ok(Self { provider, cache })
    }
}

impl<P> RPCDatabase<P>
where
    P: Transport + Clone,
{
    async fn get_balance(&mut self, address: Address) -> Result<U256, RPCError> {
        let cached_balance = self.cache.balances.get(&address);
        if let Some(&balance) = cached_balance {
            return Ok(balance);
        }

        let balance = self
            .provider
            .get_balance(address)
            .await
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_balance".to_string()))?;

        // Update the cache
        self.cache.balances.insert(address, balance);

        Ok(balance)
    }

    async fn get_nonce(&mut self, address: Address) -> Result<u64, RPCError> {
        let cached_nonce = self.cache.nonces.get(&address);
        if let Some(&nonce) = cached_nonce {
            return Ok(nonce);
        }

        let nonce = self
            .provider
            .get_transaction_count(address)
            .await
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_nonce".to_string()))?;

        self.cache.nonces.insert(address, nonce);

        Ok(nonce)
    }

    async fn get_code(&mut self, address: Address) -> Result<Bytes, RPCError> {
        let cached_code = self.cache.codes.get(&address);
        if let Some(code) = cached_code {
            return Ok(code.clone());
        }

        let code = self
            .provider
            .get_code_at(address)
            .await
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_code".to_string()))?;

        self.cache.codes.insert(address, code.clone());

        // Also update the code_hashes cache
        let code_hash = hex::encode(keccak256(&code));
        let code_hash = B256::from_str(&code_hash).unwrap();
        self.cache.code_hashes.insert(code_hash, code.clone());

        Ok(code)
    }

    // Helper function to fetch storage
    async fn get_storage(&mut self, address: Address, index: U256) -> Result<U256, RPCError> {
        let cached_storage = self.cache.storages.get(&address);
        if let Some(&storage) = cached_storage {
            return Ok(storage);
        }

        let storage = self
            .provider
            .get_storage_at(address, index)
            .await
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_storage".to_string()))?;

        self.cache.storages.insert(address, storage);

        Ok(storage)
    }

    // Helper function to fetch block hash
    async fn get_block_hash(&mut self, block_number: u64) -> Result<B256, RPCError> {
        let cached_block_hash = self.cache.block_hashes.get(&block_number);
        if let Some(&block_hash) = cached_block_hash {
            return Ok(block_hash);
        }

        let block_hash = self
            .provider
            .get_block(
                alloy_eips::BlockId::Number(alloy_eips::BlockNumberOrTag::Number(block_number)),
                alloy_rpc_types::BlockTransactionsKind::Hashes,
            )
            .await
            .map(|maybe_block| match maybe_block {
                None => Err(RPCError::RpcCallError(
                    "requested block was None".to_string(),
                    "get_block_hash".to_string(),
                )),
                Some(block) => Ok(block.header.hash),
            })
            .map_err(|e| RPCError::RpcCallError(e.to_string(), "get_block_hash".to_string()))??;

        self.cache.block_hashes.insert(block_number, block_hash);

        Ok(block_hash)
    }
}

// Blocking implementation of Database trait for revm
impl<P> revm::Database for RPCDatabase<P>
where
    P: Transport + Clone,
{
    type Error = RPCError;

    fn basic(&mut self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        // Fetch balance, nonce, and code in a blocking manner
        let balance = block_on(self.get_balance(address))?;
        let nonce = block_on(self.get_nonce(address))?;

        let (code, code_hash) = match block_on(self.get_code(address)) {
            Ok(code) => {
                let code_hash = hex::encode(keccak256(&code));
                let code_hash = B256::from_str(&code_hash).unwrap();

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

    fn code_by_hash(&mut self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        self.cache
            .code_hashes
            .get(&code_hash)
            .cloned()
            .map(|bytes| Bytecode::LegacyRaw(bytes.into()))
            .ok_or(RPCError::CodeNotFound(code_hash.to_string()))
    }

    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Self::Error> {
        // Fetch storage value at index for the provided address
        block_on(self.get_storage(address, index))
    }

    fn block_hash(&mut self, number: u64) -> Result<B256, Self::Error> {
        // Fetch the block hash for a given block number
        block_on(self.get_block_hash(number))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_node_bindings::Anvil;

    // Start an Anvil instance before running tests
    async fn start_anvil() -> RPCDatabase<Http<Client>> {
        let anvil = Anvil::new().block_time(1u64).spawn();

        let provider_url = anvil.endpoint().to_string();
        let provider = RPCDatabase::new(provider_url.as_str()).unwrap();

        provider
    }

    #[tokio::test]
    async fn mock_get_balance() {
        let mut rpc_db = start_anvil().await;

        unimplemented!()
    }

    #[tokio::test]
    async fn mock_rpc_get_nonce() {
        unimplemented!()
    }

    #[tokio::test]
    async fn mock_rpc_get_code() {
        unimplemented!()
    }

    #[tokio::test]
    async fn mock_rpc_get_storage() {
        unimplemented!()
    }

    #[tokio::test]
    async fn mock_rpc_get_block_hash() {
        unimplemented!()
    }

    #[test]
    fn integration_test_rpc_database() {
        unimplemented!()
    }
}
