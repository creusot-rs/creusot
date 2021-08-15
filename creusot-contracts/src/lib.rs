#![cfg_attr(feature = "typechecker", feature(rustc_attrs, rustc_private), feature(box_patterns, box_syntax))]

#![cfg(feature = "typechecker")]
#[macro_use]
extern crate log; 

pub use creusot_contracts_proc::*;

#[cfg(feature = "typechecker")]
pub mod typing;

#[cfg(feature = "typechecker")]
pub mod stubs;

#[cfg(feature = "typechecker")]
pub mod builtins;

#[cfg(feature = "typechecker")]
pub use builtins::*;
