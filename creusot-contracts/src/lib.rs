#![cfg_attr(feature = "contracts", feature(rustc_attrs, register_tool), register_tool(creusot))]
#![cfg_attr(feature = "typechecker", feature(rustc_private), feature(box_patterns, box_syntax))]

pub use creusot_contracts_proc::*;

#[cfg(feature = "contracts")]
pub mod stubs;

#[cfg(feature = "contracts")]
pub mod builtins;

#[cfg(feature = "contracts")]
pub use builtins::*;

