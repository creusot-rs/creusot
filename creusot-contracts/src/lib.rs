#![cfg_attr(feature = "contracts", feature(unsized_fn_params))]
#![cfg_attr(feature = "typechecker", feature(rustc_private), feature(box_patterns, box_syntax))]

pub use creusot_contracts_proc::*;

#[cfg(feature = "contracts")]
pub mod stubs;

#[cfg(feature = "contracts")]
pub mod logic;

#[cfg(feature = "contracts")]
pub use logic::*;

#[cfg(feature = "contracts")]
pub mod std;

// Re-export the rand crate
pub use rand;
