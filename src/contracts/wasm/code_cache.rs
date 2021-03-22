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

//! A module that implements instrumented code cache.
//!
//! - In order to run contract code we need to instrument it with gas metering.
//! To do that we need to provide the schedule which will supply exact gas costs values.
//! We cache this code in the storage saving the schedule version.
//! - Before running contract code we check if the cached code has the schedule version that
//! is equal to the current saved schedule.
//! If it is equal then run the code, if it isn't reinstrument with the current schedule.
//! - When we update the schedule we want it to have strictly greater version than the current saved one:
//! this guarantees that every instrumented contract code in cache cannot have the version equal to the current one.
//! Thus, before executing a contract it should be reinstrument with new schedule.

use super::{prepare, runtime::Env, PrefabWasmModule};
use super::{ContractKey, Schedule};
use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};
use std::sync::SgxMutex;
use std::vec::Vec;

lazy_static! {
    pub static ref CODE_STORAGE: SgxMutex<CodeCache> = SgxMutex::new(CodeCache::new());
}

/// Put code in the storage. The hash of code is used as a key and is returned
/// as a result of this function.
///
/// This function instruments the given code and caches it in the storage.
pub fn save(original_code: Vec<u8>, schedule: &Schedule) -> Result<ContractKey, &'static str> {
    let ref mut code_cache = CODE_STORAGE.lock().unwrap();
    code_cache.save(original_code, schedule)
}

/// Load code with the given code hash.
///
/// If the module was instrumented with a lower version of schedule than
/// the current one given as an argument, then this function will perform
/// re-instrumentation and update the cache in the storage.
pub fn load(
    contract_key: ContractKey,
    schedule: &Schedule,
) -> Result<PrefabWasmModule, &'static str> {
    let ref mut code_cache = CODE_STORAGE.lock().unwrap();
    code_cache.load(contract_key, schedule)
}

pub struct CodeCache {
    code_counter: u64,
    CodeStorage: HashMap<ContractKey, PrefabWasmModule>,
    PristineCode: HashMap<ContractKey, Vec<u8>>,
}

impl CodeCache {
    pub fn new() -> CodeCache {
        return CodeCache {
            code_counter: 0,
            CodeStorage: HashMap::new(),
            PristineCode: HashMap::new(),
        };
    }

    fn calculate_hash<T: Hash>(&mut self, t: &T) -> u64 {
        let mut s = DefaultHasher::new();

        s.write_u64(self.code_counter);
        self.code_counter += 1;

        t.hash(&mut s);
        s.finish()
    }

    pub fn save(
        &mut self,
        original_code: Vec<u8>,
        schedule: &Schedule,
    ) -> Result<ContractKey, &'static str> {
        let prefab_module = prepare::prepare_contract::<Env>(&original_code, schedule)?;
        let contract_key = self.calculate_hash(&original_code);

        self.CodeStorage.insert(contract_key, prefab_module);
        self.PristineCode.insert(contract_key, original_code);

        Ok(contract_key)
    }

    pub fn load(
        &mut self,
        contract_key: ContractKey,
        schedule: &Schedule,
    ) -> Result<PrefabWasmModule, &'static str> {
        let prefab_module = self
            .CodeStorage
            .get(&contract_key)
            .ok_or_else(|| "code is not found")?;

        Ok(prefab_module.clone())
    }
}
