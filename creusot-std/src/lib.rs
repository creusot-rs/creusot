//! The "standard library" of Creusot.
//!
//! To start using Creusot, you should always import that crate. The recommended way is
//! to have a glob import:
//!
//! ```
//! use creusot_std::prelude::*;
//! ```
//!
//! # Writing specifications
//!
//! To start writing specification, use the [`requires`][crate::macros::requires] and [`ensures`][crate::macros::ensures] macros:
//!
//! ```
//! use creusot_std::prelude::*;
//!
//! #[requires(x < i32::MAX)]
//! #[ensures(result@ == x@ + 1)]
//! fn add_one(x: i32) -> i32 {
//!     x + 1
//! }
//! ```
//!
//! For a more detailed explanation, see the [guide](https://guide.creusot.rs).
//!
//! # Module organization
//!
//! 1. Core features of Creusot
//!
//!     - [`invariant`][mod@invariant]: Type invariants
//!     - [`macros`]: `#[requires]`, `#[ensures]`, etc.
//!     - [`resolve`][mod@resolve]: Resolve mutable borrows
//!     - [`model`]: `View` and `DeepModel`
//!     - [`snapshot`][mod@snapshot]: Snapshots
//!
//! 2. [`logic`][mod@logic]: Logical structures used in specifications
//!
//! 3. [`ghost`][mod@ghost]: Ghost code
//!
//! 4. [`std`][mod@std]: Specifications for the `std` crate
//!
//! 5. [`cell`][mod@cell]: Interior mutability
//!
//! 6. [`peano`]: Peano integers
//!
//! 7. [`prelude`][mod@prelude]: What you should import before doing anything with Creusot
#![cfg_attr(feature = "nightly", allow(incomplete_features, internal_features))]
#![cfg_attr(
    feature = "nightly",
    feature(step_trait, unboxed_closures, tuple_trait, edition_panic, sync_unsafe_cell)
)]
#![cfg_attr(all(feature = "nightly", feature = "std"), feature(allocator_api))]
#![cfg_attr(
    creusot,
    feature(
        core_intrinsics,
        const_destruct,
        fn_traits,
        fmt_arguments_from_str,
        fmt_helpers_for_derive,
        try_trait_v2,
        try_trait_v2_residual,
        panic_internals,
        ptr_metadata,
        hint_must_use,
        pointer_is_aligned_to,
        range_bounds_is_empty,
        bound_copied,
        auto_traits,
        negative_impls,
        exact_size_is_empty,
        sized_hierarchy,
        nonzero_internals,
    )
)]
#![cfg_attr(all(doc, feature = "nightly"), feature(intra_doc_pointers))]
#![cfg_attr(all(creusot, feature = "std"), feature(print_internals, libstd_sys_internals, rt,))]
#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit = "512"]

extern crate creusot_std_proc as base_macros;
extern crate self as creusot_std;

/// Specification are written using these macros
///
/// All of those are re-exported at the top of the crate.
pub mod macros;

#[doc(hidden)]
#[cfg(creusot)]
#[path = "stubs.rs"]
pub mod __stubs;

pub mod cell;
pub mod ghost;
pub mod invariant;
pub mod logic;
pub mod model;
pub mod peano;
pub mod resolve;
pub mod snapshot;
pub mod std;

// We add some common things at the root of the creusot-std library
mod base_prelude {
    pub use crate::{
        ghost::Ghost,
        invariant::Invariant,
        logic::{Int, OrdLogic, PartialOrdLogic, Seq, ops::IndexLogic as _},
        model::{DeepModel, View},
        resolve::Resolve,
        snapshot::Snapshot,
        std::iter::{DoubleEndedIteratorSpec, IteratorSpec},
    };

    pub use crate::std::{
        // Shadow std::prelude by our version of derive macros and of vec!.
        // If the user write the glob pattern "use creusot_std::prelude::*",
        // then rustc will either shadow the old identifier or complain about
        // the ambiguity (ex: for the derive macros Clone and PartialEq, a glob
        // pattern is not enough to force rustc to use our version, but at least
        // we get an error message).
        clone::Clone,
        cmp::PartialEq,
        default::Default,
    };

    #[cfg(feature = "std")]
    pub use crate::std::vec::vec;

    // Export extension traits anonymously
    pub use crate::std::{
        char::CharExt as _,
        iter::{SkipExt as _, TakeExt as _},
        num::NumExt as _,
        ops::{FnExt as _, FnMutExt as _, FnOnceExt as _, RangeInclusiveExt as _},
        option::OptionExt as _,
        ptr::{PointerExt as _, PtrAddExt as _, SizedPointerExt as _, SlicePointerExt as _},
        slice::SliceExt as _,
    };

    #[cfg(creusot)]
    pub use crate::{invariant::inv, resolve::resolve};
}
/// Basic features to get started with Creusot.
pub mod prelude {
    pub use crate::{base_prelude::*, macros::*};
}
