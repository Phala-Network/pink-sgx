#![cfg_attr(not(target_env = "sgx"), no_std)]
#![cfg_attr(target_env = "sgx", feature(rustc_private))]

extern crate sgx_types;
#[cfg(not(target_env = "sgx"))]
#[macro_use]
extern crate sgx_tstd as std;
#[macro_use]
extern crate lazy_static;
extern crate wabt;
extern crate wasmi;

use std::prelude::v1::*;

pub use wasmi::Error as InterpreterError;

extern crate serde;
#[macro_use]
extern crate serde_derive;

mod allocator;
mod contracts;
mod executor;
mod sandbox;
mod wasm_interface;

pub use contracts::InkModule;
