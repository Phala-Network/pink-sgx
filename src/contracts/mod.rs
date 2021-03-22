// Copyright 2018-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! # Contract Module
//!
//! The Contract module provides functionality for the runtime to deploy and execute WebAssembly smart-contracts.
//!
//! - [`contract::Config`](./trait.Config.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! This module extends accounts based on the `Currency` trait to have smart-contract functionality. It can
//! be used with other modules that implement accounts based on `Currency`. These "smart-contract accounts"
//! have the ability to instantiate smart-contracts and make calls to other contract and non-contract accounts.
//!
//! The smart-contract code is stored once in a `code_cache`, and later retrievable via its `code_hash`.
//! This means that multiple smart-contracts can be instantiated from the same `code_cache`, without replicating
//! the code each time.
//!
//! When a smart-contract is called, its associated code is retrieved via the code hash and gets executed.
//! This call can alter the storage entries of the smart-contract account, instantiate new smart-contracts,
//! or call other smart-contracts.
//!
//! Finally, when an account is reaped, its associated code and storage of the smart-contract account
//! will also be deleted.
//!
//! ### Gas
//!
//! Senders must specify a gas limit with every call, as all instructions invoked by the smart-contract require gas.
//! Unused gas is refunded after the call, regardless of the execution outcome.
//!
//! If the gas limit is reached, then all calls and state changes (including balance transfers) are only
//! reverted at the current call's contract level. For example, if contract A calls B and B runs out of gas mid-call,
//! then all of B's calls are reverted. Assuming correct error handling by contract A, A's other calls and state
//! changes still persist.
//!
//! ### Notable Scenarios
//!
//! Contract call failures are not always cascading. When failures occur in a sub-call, they do not "bubble up",
//! and the call will only revert at the specific contract level. For example, if contract A calls contract B, and B
//! fails, A can decide how to handle that failure, either proceeding or reverting A's changes.
//!
//! ## Interface
//!
//! ### Dispatchable functions
//!
//! * `put_code` - Stores the given binary Wasm code into the chain's storage and returns its `code_hash`.
//! * `instantiate` - Deploys a new contract from the given `code_hash`, optionally transferring some balance.
//! This instantiates a new smart contract account and calls its contract deploy handler to
//! initialize the contract.
//! * `call` - Makes a call to an account, optionally transferring some balance.
//!
//! ## Usage
//!
//! The Contract module is a work in progress. The following examples show how this Contract module
//! can be used to instantiate and call contracts.
//!
//! * [`ink`](https://github.com/paritytech/ink) is
//! an [`eDSL`](https://wiki.haskell.org/Embedded_domain_specific_language) that enables writing
//! WebAssembly based smart contracts in the Rust programming language. This is a work in progress.
//!
//! ## Related Modules
//!
//! * [Balances](../pallet_balances/index.html)

mod exec;
mod primitives;
mod schedule;
mod storage;
mod wasm;
pub mod weights;

use super::sandbox;
use exec::ExecutionContext;
pub use exec::{ContractKey, StorageKey};
use primitives::{DispatchError, DispatchResult, ExecResult, GetStorageResult};
pub use schedule::{HostFnWeights, InstructionWeights, Limits, Schedule};
use storage::Storage;
pub use wasm::ReturnCode as RuntimeReturnCode;
use wasm::{WasmLoader, WasmVm};
pub use weights::WeightInfo;

use codec::{Decode, Encode};
use std::vec::Vec;

/// The maximum nesting level of a call/instantiate stack. A reasonable default
/// value is 100.
const MAX_DEPTH: u32 = 100;

/// The maximum size of a storage value in bytes. A reasonable default is 16 KiB.
const MAX_VALUE_SIZE: u32 = 16 * 1024;

/// Error for the contracts module.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, Debug)]
pub enum Error {
    /// A new schedule must have a greater version than the current one.
    InvalidScheduleVersion,
    /// An origin must be signed or inherent and auxiliary sender only provided on inherent.
    InvalidSurchargeClaim,
    /// Cannot restore from nonexisting or tombstone contract.
    InvalidSourceContract,
    /// Cannot restore to nonexisting or alive contract.
    InvalidDestinationContract,
    /// Tombstones don't match.
    InvalidTombstone,
    /// An origin TrieId written in the current block.
    InvalidContractOrigin,
    /// The executed contract exhausted its gas limit.
    OutOfGas,
    /// The output buffer supplied to a contract API call was too small.
    OutputBufferTooSmall,
    /// Performing the requested transfer would have brought the contract below
    /// the subsistence threshold. No transfer is allowed to do this in order to allow
    /// for a tombstone to be created. Use `seal_terminate` to remove a contract without
    /// leaving a tombstone behind.
    BelowSubsistenceThreshold,
    /// The newly created contract is below the subsistence threshold after executing
    /// its contructor. No contracts are allowed to exist below that threshold.
    NewContractNotFunded,
    /// Performing the requested transfer failed for a reason originating in the
    /// chosen currency implementation of the runtime. Most probably the balance is
    /// too low or locks are placed on it.
    TransferFailed,
    /// Performing a call was denied because the calling depth reached the limit
    /// of what is specified in the schedule.
    MaxCallDepthReached,
    /// The contract that was called is either no contract at all (a plain account)
    /// or is a tombstone.
    NotCallable,
    /// The code supplied to `put_code` exceeds the limit specified in the current schedule.
    CodeTooLarge,
    /// No code could be found at the supplied code hash.
    CodeNotFound,
    /// A buffer outside of sandbox memory was passed to a contract API function.
    OutOfBounds,
    /// Input passed to a contract API function failed to decode as expected type.
    DecodingFailed,
    /// Contract trapped during execution.
    ContractTrapped,
    /// The size defined in `T::MaxValueSize` was exceeded.
    ValueTooLarge,
    /// The action performed is not allowed while the contract performing it is already
    /// on the call stack. Those actions are contract self destruction and restoration
    /// of a tombstone.
    ReentranceDenied,
}

impl From<Error> for DispatchError {
    fn from(err: Error) -> Self {
        DispatchError::Module(err)
    }
}

/// Contracts module.
pub struct InkModule {
    cfg: ConfigCache,
}

impl InkModule {
    pub fn new() -> InkModule {
        InkModule {
            cfg: ConfigCache::preload(),
        }
    }

    // /// Updates the schedule for metering contracts.
    // ///
    // /// The schedule must have a greater version than the stored schedule.
    // pub fn update_schedule(origin, schedule: Schedule<T>) -> DispatchResult {
    //     ensure_root(origin)?;
    //     if <Module<T>>::current_schedule().version >= schedule.version {
    //         Err(Error::InvalidScheduleVersion)?
    //     }

    //     Self::deposit_event(RawEvent::ScheduleUpdated(schedule.version));
    //     CurrentSchedule::put(schedule);

    //     Ok(())
    // }

    /// Stores the given binary Wasm code into the chain's storage and returns its `codehash`.
    /// You can instantiate contracts only with stored code.
    pub fn put_code(&mut self, code: Vec<u8>) -> std::result::Result<ContractKey, DispatchError> {
        if code.len() as u32 > self.cfg.schedule.limits.code_size {
            return Err(DispatchError::Module(Error::CodeTooLarge));
        }

        let result = wasm::save_code(code, &self.cfg.schedule);
        result.map_err(DispatchError::Other)
    }

    /// Makes a call to an account, optionally transferring some balance.
    ///
    /// * If the account is a smart-contract account, the associated code will be
    /// executed and any value will be transferred.
    /// * If the account is a regular account, any value will be transferred.
    /// * If no account exists and the call value is not less than `existential_deposit`,
    /// a regular account will be created and any value will be transferred.
    pub fn call(dest: ContractKey, data: Vec<u8>) -> ExecResult {
        Self::execute_wasm(|ctx| ctx.call(dest, data))
    }

    /// Instantiates a new contract from the `code_hash` generated by `put_code`,
    /// optionally transferring some balance.
    ///
    /// The supplied `salt` is used for contract address deriviation. See `fn contract_address`.
    ///
    /// Instantiation is executed as follows:
    ///
    /// - The destination address is computed based on the sender, code_hash and the salt.
    /// - The smart-contract account is created at the computed address.
    /// - The `ctor_code` is executed in the context of the newly-created account. Buffer returned
    ///   after the execution is saved as the `code` of the account. That code will be invoked
    ///   upon any call received by this account.
    /// - The contract is initialized.
    pub fn instantiate(code: ContractKey, data: Vec<u8>) -> ExecResult {
        Self::execute_wasm(|ctx| ctx.instantiate(code, data))
    }
}

/// Public APIs provided by the contracts module.
impl InkModule {
    /// Perform a call to a specified contract.
    ///
    /// This function is similar to `Self::call`, but doesn't perform any address lookups and better
    /// suitable for calling directly from Rust.
    ///
    /// It returns the exection result and the amount of used weight.
    pub fn bare_call(dest: ContractKey, input_data: Vec<u8>) -> ExecResult {
        Self::execute_wasm(|ctx| ctx.call(dest, input_data))
    }

    /// Query storage of a specified contract under a specified key.
    pub fn get_storage(address: ContractKey, key: [u8; 32]) -> GetStorageResult {
        let maybe_value = Storage::read(address, &key);
        Ok(maybe_value)
    }
}

impl InkModule {
    fn execute_wasm(
        func: impl FnOnce(&mut ExecutionContext<WasmVm, WasmLoader>) -> ExecResult,
    ) -> ExecResult {
        let cfg = ConfigCache::preload();
        let vm = WasmVm::new(&cfg.schedule);
        let loader = WasmLoader::new(&cfg.schedule);
        let mut ctx = ExecutionContext::top_level(&cfg, &vm, &loader);
        func(&mut ctx)
    }
}

/// In-memory cache of configuration values.
///
/// We assume that these values can't be changed in the
/// course of transaction execution.
pub struct ConfigCache {
    pub schedule: Schedule,
    pub max_depth: u32,
    pub max_value_size: u32,
}

impl ConfigCache {
    fn preload() -> ConfigCache {
        ConfigCache {
            schedule: Default::default(),
            max_depth: MAX_DEPTH,
            max_value_size: MAX_VALUE_SIZE,
        }
    }
}
