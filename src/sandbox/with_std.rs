// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::borrow::ToOwned;
use std::boxed::Box;
use std::collections::btree_map::BTreeMap;
use std::fmt;
use std::vec::Vec;

use super::{Error, HostError, HostFuncType, ReturnValue, Value};
use serde::{Deserialize, Serialize};
use wasmi::memory_units::Pages;
use wasmi::{
    Externals, FuncInstance, FuncRef, GlobalDescriptor, GlobalRef, ImportResolver,
    MemoryDescriptor, MemoryInstance, MemoryRef, Module, ModuleInstance, ModuleRef, RuntimeArgs,
    RuntimeValue, Signature, TableDescriptor, TableRef, Trap, TrapKind,
};

#[derive(Clone)]
pub struct Memory {
    memref: MemoryRef,
}

impl Memory {
    pub fn new(initial: u32, maximum: Option<u32>) -> Result<Memory, Error> {
        Ok(Memory {
            memref: MemoryInstance::alloc(
                Pages(initial as usize),
                maximum.map(|m| Pages(m as usize)),
            )
            .map_err(|_| Error::Module)?,
        })
    }

    pub fn get(&self, ptr: u32, buf: &mut [u8]) -> Result<(), Error> {
        self.memref
            .get_into(ptr, buf)
            .map_err(|_| Error::OutOfBounds)?;
        Ok(())
    }

    pub fn set(&self, ptr: u32, value: &[u8]) -> Result<(), Error> {
        self.memref
            .set(ptr, value)
            .map_err(|_| Error::OutOfBounds)?;
        Ok(())
    }
}

struct HostFuncIndex(usize);

struct DefinedHostFunctions<T> {
    funcs: Vec<HostFuncType<T>>,
}

impl<T> Clone for DefinedHostFunctions<T> {
    fn clone(&self) -> DefinedHostFunctions<T> {
        DefinedHostFunctions {
            funcs: self.funcs.clone(),
        }
    }
}

impl<T> DefinedHostFunctions<T> {
    fn new() -> DefinedHostFunctions<T> {
        DefinedHostFunctions { funcs: Vec::new() }
    }

    fn define(&mut self, f: HostFuncType<T>) -> HostFuncIndex {
        let idx = self.funcs.len();
        self.funcs.push(f);
        HostFuncIndex(idx)
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct DummyHostError;

impl fmt::Display for DummyHostError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DummyHostError")
    }
}

impl wasmi::HostError for DummyHostError {
    fn typetag_name(&self) -> &'static str {
        "DummyHostError"
    }

    #[doc(hidden)]
    fn typetag_deserialize(&self) {}
}

struct GuestExternals<'a, T: 'a> {
    state: &'a mut T,
    defined_host_functions: &'a DefinedHostFunctions<T>,
}

impl<'a, T> Externals for GuestExternals<'a, T> {
    fn invoke_index(
        &mut self,
        index: usize,
        args: RuntimeArgs,
    ) -> Result<Option<RuntimeValue>, Trap> {
        let args = args
            .as_ref()
            .iter()
            .cloned()
            .map(Into::into)
            .collect::<Vec<_>>();

        let result = (self.defined_host_functions.funcs[index])(self.state, &args);
        match result {
            Ok(value) => Ok(match value {
                ReturnValue::Value(v) => Some(v.into()),
                ReturnValue::Unit => None,
            }),
            Err(HostError) => Err(TrapKind::Host(Box::new(DummyHostError)).into()),
        }
    }
}

enum ExternVal {
    HostFunc(HostFuncIndex),
    Memory(Memory),
}

pub struct EnvironmentDefinitionBuilder<T> {
    map: BTreeMap<(Vec<u8>, Vec<u8>), ExternVal>,
    defined_host_functions: DefinedHostFunctions<T>,
}

impl<T> EnvironmentDefinitionBuilder<T> {
    pub fn new() -> EnvironmentDefinitionBuilder<T> {
        EnvironmentDefinitionBuilder {
            map: BTreeMap::new(),
            defined_host_functions: DefinedHostFunctions::new(),
        }
    }

    pub fn add_host_func<N1, N2>(&mut self, module: N1, field: N2, f: HostFuncType<T>)
    where
        N1: Into<Vec<u8>>,
        N2: Into<Vec<u8>>,
    {
        let idx = self.defined_host_functions.define(f);
        self.map
            .insert((module.into(), field.into()), ExternVal::HostFunc(idx));
    }

    pub fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
    where
        N1: Into<Vec<u8>>,
        N2: Into<Vec<u8>>,
    {
        self.map
            .insert((module.into(), field.into()), ExternVal::Memory(mem));
    }
}

impl<T> ImportResolver for EnvironmentDefinitionBuilder<T> {
    fn resolve_func(
        &self,
        module_name: &str,
        field_name: &str,
        signature: &Signature,
    ) -> Result<FuncRef, wasmi::Error> {
        let key = (
            module_name.as_bytes().to_owned(),
            field_name.as_bytes().to_owned(),
        );
        let externval = self.map.get(&key).ok_or_else(|| {
            wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
        })?;
        let host_func_idx = match *externval {
            ExternVal::HostFunc(ref idx) => idx,
            _ => {
                return Err(wasmi::Error::Instantiation(format!(
                    "Export {}:{} is not a host func",
                    module_name, field_name
                )))
            }
        };
        Ok(FuncInstance::alloc_host(signature.clone(), host_func_idx.0))
    }

    fn resolve_global(
        &self,
        _module_name: &str,
        _field_name: &str,
        _global_type: &GlobalDescriptor,
    ) -> Result<GlobalRef, wasmi::Error> {
        Err(wasmi::Error::Instantiation(format!(
            "Importing globals is not supported yet"
        )))
    }

    fn resolve_memory(
        &self,
        module_name: &str,
        field_name: &str,
        _memory_type: &MemoryDescriptor,
    ) -> Result<MemoryRef, wasmi::Error> {
        let key = (
            module_name.as_bytes().to_owned(),
            field_name.as_bytes().to_owned(),
        );
        let externval = self.map.get(&key).ok_or_else(|| {
            wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
        })?;
        let memory = match *externval {
            ExternVal::Memory(ref m) => m,
            _ => {
                return Err(wasmi::Error::Instantiation(format!(
                    "Export {}:{} is not a memory",
                    module_name, field_name
                )))
            }
        };
        Ok(memory.memref.clone())
    }

    fn resolve_table(
        &self,
        _module_name: &str,
        _field_name: &str,
        _table_type: &TableDescriptor,
    ) -> Result<TableRef, wasmi::Error> {
        Err(wasmi::Error::Instantiation(format!(
            "Importing tables is not supported yet"
        )))
    }
}

pub struct Instance<T> {
    instance: ModuleRef,
    defined_host_functions: DefinedHostFunctions<T>,
    _marker: std::marker::PhantomData<T>,
}

impl<T> Instance<T> {
    pub fn new(
        code: &[u8],
        env_def_builder: &EnvironmentDefinitionBuilder<T>,
        state: &mut T,
    ) -> Result<Instance<T>, Error> {
        let module = Module::from_buffer(code).map_err(|_| Error::Module)?;
        let not_started_instance =
            ModuleInstance::new(&module, env_def_builder).map_err(|_| Error::Module)?;

        let defined_host_functions = env_def_builder.defined_host_functions.clone();
        let instance = {
            let mut externals = GuestExternals {
                state,
                defined_host_functions: &defined_host_functions,
            };
            let instance = not_started_instance
                .run_start(&mut externals)
                .map_err(|_| Error::Execution)?;
            instance
        };

        Ok(Instance {
            instance,
            defined_host_functions,
            _marker: std::marker::PhantomData::<T>,
        })
    }

    pub fn invoke(
        &mut self,
        name: &str,
        args: &[Value],
        state: &mut T,
    ) -> Result<ReturnValue, Error> {
        let args = args.iter().cloned().map(Into::into).collect::<Vec<_>>();

        let mut externals = GuestExternals {
            state,
            defined_host_functions: &self.defined_host_functions,
        };
        let result = self.instance.invoke_export(&name, &args, &mut externals);

        match result {
            Ok(None) => Ok(ReturnValue::Unit),
            Ok(Some(val)) => Ok(ReturnValue::Value(val.into())),
            Err(_err) => Err(Error::Execution),
        }
    }

    pub fn get_global_val(&self, name: &str) -> Option<Value> {
        let global = self.instance.export_by_name(name)?.as_global()?.get();

        Some(global.into())
    }
}

#[cfg(test)]
mod tests {
    use crate::{EnvironmentDefinitionBuilder, Error, HostError, Instance, ReturnValue, Value};
    use assert_matches::assert_matches;

    fn execute_sandboxed(code: &[u8], args: &[Value]) -> Result<ReturnValue, HostError> {
        struct State {
            counter: u32,
        }

        fn env_assert(_e: &mut State, args: &[Value]) -> Result<ReturnValue, HostError> {
            if args.len() != 1 {
                return Err(HostError);
            }
            let condition = args[0].as_i32().ok_or_else(|| HostError)?;
            if condition != 0 {
                Ok(ReturnValue::Unit)
            } else {
                Err(HostError)
            }
        }
        fn env_inc_counter(e: &mut State, args: &[Value]) -> Result<ReturnValue, HostError> {
            if args.len() != 1 {
                return Err(HostError);
            }
            let inc_by = args[0].as_i32().ok_or_else(|| HostError)?;
            e.counter += inc_by as u32;
            Ok(ReturnValue::Value(Value::I32(e.counter as i32)))
        }
        /// Function that takes one argument of any type and returns that value.
        fn env_polymorphic_id(_e: &mut State, args: &[Value]) -> Result<ReturnValue, HostError> {
            if args.len() != 1 {
                return Err(HostError);
            }
            Ok(ReturnValue::Value(args[0]))
        }

        let mut state = State { counter: 0 };

        let mut env_builder = EnvironmentDefinitionBuilder::new();
        env_builder.add_host_func("env", "assert", env_assert);
        env_builder.add_host_func("env", "inc_counter", env_inc_counter);
        env_builder.add_host_func("env", "polymorphic_id", env_polymorphic_id);

        let mut instance = Instance::new(code, &env_builder, &mut state)?;
        let result = instance.invoke("call", args, &mut state);

        result.map_err(|_| HostError)
    }

    #[test]
    fn invoke_args() {
        let code = wat::parse_str(
            r#"
		(module
			(import "env" "assert" (func $assert (param i32)))

			(func (export "call") (param $x i32) (param $y i64)
				;; assert that $x = 0x12345678
				(call $assert
					(i32.eq
						(get_local $x)
						(i32.const 0x12345678)
					)
				)

				(call $assert
					(i64.eq
						(get_local $y)
						(i64.const 0x1234567887654321)
					)
				)
			)
		)
		"#,
        )
        .unwrap();

        let result = execute_sandboxed(
            &code,
            &[Value::I32(0x12345678), Value::I64(0x1234567887654321)],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn return_value() {
        let code = wat::parse_str(
            r#"
		(module
			(func (export "call") (param $x i32) (result i32)
				(i32.add
					(get_local $x)
					(i32.const 1)
				)
			)
		)
		"#,
        )
        .unwrap();

        let return_val = execute_sandboxed(&code, &[Value::I32(0x1336)]).unwrap();
        assert_eq!(return_val, ReturnValue::Value(Value::I32(0x1337)));
    }

    #[test]
    fn signatures_dont_matter() {
        let code = wat::parse_str(
            r#"
		(module
			(import "env" "polymorphic_id" (func $id_i32 (param i32) (result i32)))
			(import "env" "polymorphic_id" (func $id_i64 (param i64) (result i64)))
			(import "env" "assert" (func $assert (param i32)))

			(func (export "call")
				;; assert that we can actually call the "same" function with different
				;; signatures.
				(call $assert
					(i32.eq
						(call $id_i32
							(i32.const 0x012345678)
						)
						(i32.const 0x012345678)
					)
				)
				(call $assert
					(i64.eq
						(call $id_i64
							(i64.const 0x0123456789abcdef)
						)
						(i64.const 0x0123456789abcdef)
					)
				)
			)
		)
		"#,
        )
        .unwrap();

        let return_val = execute_sandboxed(&code, &[]).unwrap();
        assert_eq!(return_val, ReturnValue::Unit);
    }

    #[test]
    fn cant_return_unmatching_type() {
        fn env_returns_i32(_e: &mut (), _args: &[Value]) -> Result<ReturnValue, HostError> {
            Ok(ReturnValue::Value(Value::I32(42)))
        }

        let mut env_builder = EnvironmentDefinitionBuilder::new();
        env_builder.add_host_func("env", "returns_i32", env_returns_i32);

        let code = wat::parse_str(
            r#"
		(module
			;; It's actually returns i32, but imported as if it returned i64
			(import "env" "returns_i32" (func $returns_i32 (result i64)))

			(func (export "call")
				(drop
					(call $returns_i32)
				)
			)
		)
		"#,
        )
        .unwrap();

        // It succeeds since we are able to import functions with types we want.
        let mut instance = Instance::new(&code, &env_builder, &mut ()).unwrap();

        // But this fails since we imported a function that returns i32 as if it returned i64.
        assert_matches!(instance.invoke("call", &[], &mut ()), Err(Error::Execution));
    }
}
