// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! A crate that hosts a common definitions that are relevant for the pallet-contracts.

use super::Error;
use bitflags::bitflags;
use codec::{Decode, Encode};
use std::vec::Vec;

/// Result of a `Dispatchable` which contains the `DispatchResult` and additional information about
/// the `Dispatchable` that is only known post dispatch.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, Debug)]
pub struct DispatchErrorWithPostInfo<Info>
where
    Info: Eq + PartialEq + Clone + Copy + Encode + Decode,
{
    /// Additional information about the `Dispatchable` which is only known post dispatch.
    pub post_info: Info,
    /// The actual `DispatchResult` indicating whether the dispatch was successful.
    pub error: DispatchError,
}

/// This is the legacy return type of `Dispatchable`. It is still exposed for compatibility reasons.
/// The new return type is `DispatchResultWithInfo`. FRAME runtimes should use
/// `frame_support::dispatch::DispatchResult`.
pub type DispatchResult = std::result::Result<(), DispatchError>;

/// Return type of a `Dispatchable` which contains the `DispatchResult` and additional information
/// about the `Dispatchable` that is only known post dispatch.
pub type DispatchResultWithInfo<T> = std::result::Result<T, DispatchErrorWithPostInfo<T>>;

#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, Debug)]
pub enum DispatchError {
    /// Some error occurred.
    Other(#[codec(skip)] &'static str),
    /// Failed to lookup some data.
    CannotLookup,
    /// A bad origin.
    BadOrigin,
    /// A custom error in a module.
    Module(Error),
}

impl From<&'static str> for DispatchError {
    fn from(err: &'static str) -> Self {
        DispatchError::Other(err)
    }
}

/// Result type of a `bare_call` call.
///
/// The result of a contract execution along with a gas consumed.
#[derive(Eq, PartialEq, Encode, Decode, Debug)]
pub struct ContractExecResult {
    pub exec_result: ExecResult,
    pub gas_consumed: u64,
}

/// Result type of a `get_storage` call.
pub type GetStorageResult = Result<Option<Vec<u8>>, ContractAccessError>;

/// Result type of a `rent_projection` call.
pub type RentProjectionResult<BlockNumber> =
    Result<RentProjection<BlockNumber>, ContractAccessError>;

/// The possible errors that can happen querying the storage of a contract.
#[derive(Eq, PartialEq, Encode, Decode, Debug)]
pub enum ContractAccessError {
    /// The given address doesn't point to a contract.
    DoesntExist,
    /// The specified contract is a tombstone and thus cannot have any storage.
    IsTombstone,
}

#[derive(Eq, PartialEq, Encode, Decode, Debug)]
pub enum RentProjection<BlockNumber> {
    /// Eviction is projected to happen at the specified block number.
    EvictionAt(BlockNumber),
    /// No eviction is scheduled.
    ///
    /// E.g. Contract accumulated enough funds to offset the rent storage costs.
    NoEviction,
}

bitflags! {
    /// Flags used by a contract to customize exit behaviour.
    #[derive(Encode, Decode)]
    pub struct ReturnFlags: u32 {
        /// If this bit is set all changes made by the contract execution are rolled back.
        const REVERT = 0x0000_0001;
    }
}

/// Output of a contract call or instantiation which ran to completion.
#[derive(PartialEq, Eq, Encode, Decode, Debug)]
pub struct ExecReturnValue {
    /// Flags passed along by `seal_return`. Empty when `seal_return` was never called.
    pub flags: ReturnFlags,
    /// Buffer passed along by `seal_return`. Empty when `seal_return` was never called.
    pub data: Vec<u8>,
}

impl ExecReturnValue {
    /// We understand the absense of a revert flag as success.
    pub fn is_success(&self) -> bool {
        !self.flags.contains(ReturnFlags::REVERT)
    }
}

/// Origin of the error.
///
/// Call or instantiate both called into other contracts and pass through errors happening
/// in those to the caller. This enum is for the caller to distinguish whether the error
/// happened during the execution of the callee or in the current execution context.
#[derive(PartialEq, Eq, Encode, Decode, Debug)]
pub enum ErrorOrigin {
    /// Caller error origin.
    ///
    /// The error happened in the current exeuction context rather than in the one
    /// of the contract that is called into.
    Caller,
    /// The error happened during execution of the called contract.
    Callee,
}

/// Error returned by contract exection.
#[derive(PartialEq, Eq, Encode, Decode, Debug)]
pub struct ExecError {
    /// The reason why the execution failed.
    pub error: DispatchError,
    /// Origin of the error.
    pub origin: ErrorOrigin,
}

impl<T: Into<DispatchError>> From<T> for ExecError {
    fn from(error: T) -> Self {
        Self {
            error: error.into(),
            origin: ErrorOrigin::Caller,
        }
    }
}

/// The result that is returned from contract execution. It either contains the output
/// buffer or an error describing the reason for failure.
pub type ExecResult = Result<ExecReturnValue, ExecError>;
