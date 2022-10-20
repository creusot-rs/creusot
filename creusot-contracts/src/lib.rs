#![cfg_attr(
    feature = "contracts",
    feature(unsized_locals, fn_traits, unboxed_closures, min_specialization, allocator_api),
    allow(incomplete_features),
    feature(slice_take)
)]
#![cfg_attr(feature = "typechecker", feature(rustc_private), feature(box_patterns, box_syntax))]

#[cfg(feature = "contracts")]
extern crate creusot_contracts_proc as base_macros;

#[cfg(not(feature = "contracts"))]
extern crate creusot_contracts_dummy as base_macros;

mod macros {
    /// A pre-condition of a function or trait item
    pub use base_macros::requires;

    /// A post-condition of a function or trait item
    pub use base_macros::ensures;

    pub use base_macros::ghost;

    /// A loop invariant
    /// The first argument should be a name for the invariant
    /// The second argument is the Pearlite expression for the loop invariant
    pub use base_macros::invariant;

    /// Declares a trait item as being a law which is autoloaded as soon another
    /// trait item is used in a function
    pub use base_macros::law;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs as it is *ghost*, in exchange it can
    /// use logical operations and syntax with the help of the [pearlite] macro.
    pub use base_macros::logic;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs as it is *ghost*, in exchange it can
    /// use logical operations and syntax with the help of the [pearlite] macro.
    pub use base_macros::predicate;

    /// Inserts a *logical* assertion into the code. This assertion will not be checked at runtime
    /// but only during proofs. However, it has access to the ghost context and can use logical operations
    /// and syntax.
    pub use base_macros::proof_assert;

    /// Instructs Pearlite to ignore the body of a declaration, assuming any contract the declaration has is
    /// valid.
    pub use base_macros::trusted;

    /// Declares a variant for a function, this is primarily used in combination with logical functions
    /// The variant must be an expression which returns a type implementing [WellFounded]
    pub use base_macros::variant;

    /// Enables Pearlite syntax, granting access to Pearlite specific operators and syntax
    pub use base_macros::pearlite;

    /// Allows specifications to be attached to functions coming from external crates
    /// TODO: Document syntax
    pub use base_macros::extern_spec;

    /// Allows specifying both a pre- and post-condition in a single statement.
    /// Expects an expression in either the form of a method or function call
    /// Arguments to the call can be prefixed with `mut` to indicate that they are mutable borrows.
    ///
    /// Generates a `requires` and `ensures` clause in the shape of the input expression, with
    /// `mut` replaced by `*` in the `requires` and `^` in the ensures.
    pub use base_macros::maintains;

    pub mod prusti {
        pub use base_macros::{
            prusti_ensures as ensures, prusti_ensures_expiry as after_expiry,
            prusti_requires as requires,
        };
    }
}

pub use macros::*;

#[cfg(feature = "contracts")]
pub mod derive {
    pub use creusot_contracts_proc::{Clone, PartialEq};
}

#[cfg(not(feature = "contracts"))]
pub mod derive {
    pub use ::std::{clone::Clone, cmp::PartialEq};
}

#[cfg(feature = "contracts")]
#[path = "stubs.rs"]
pub mod __stubs;

pub mod logic;

#[cfg(feature = "contracts")]
pub mod std;

#[cfg(not(feature = "contracts"))]
pub mod std {}

#[cfg(feature = "contracts")]
mod ghost;

#[cfg(not(feature = "contracts"))]
mod ghost {
    pub struct Ghost<T>(std::marker::PhantomData<T>)
    where
        T: ?Sized;

    impl<T> Ghost<T> {
        pub fn new() -> Ghost<T> {
            Ghost(std::marker::PhantomData)
        }
    }
}

mod model;
mod resolve;
mod well_founded;

pub use ghost::Ghost;
pub use model::{DeepModel, ShallowModel};
pub use resolve::Resolve;
pub use well_founded::WellFounded;
