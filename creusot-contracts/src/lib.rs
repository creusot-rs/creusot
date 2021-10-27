#![cfg_attr(feature = "contracts", feature(unsized_fn_params))]
#![cfg_attr(feature = "typechecker", feature(rustc_private), feature(box_patterns, box_syntax))]

pub use creusot_contracts_proc::*;

#[cfg(feature = "contracts")]
pub mod stubs;

#[cfg(feature = "contracts")]
pub mod builtins;

#[cfg(feature = "contracts")]
pub use builtins::*;

#[cfg(feature = "contracts")]
pub mod std;

#[cfg(feature = "contracts")]
pub use crate::std::WellFounded;

// Re-export the rand crate
pub use rand;
