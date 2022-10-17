#![cfg_attr(
    feature = "contracts",
    feature(unsized_locals, fn_traits, min_specialization),
    allow(incomplete_features),
    feature(slice_take)
)]
#![cfg_attr(feature = "typechecker", feature(rustc_private), feature(box_patterns, box_syntax))]
#![feature(step_trait, allocator_api, unboxed_closures)]
#![cfg_attr(not(feature = "contracts"), feature(rustc_attrs))]

extern crate self as creusot_contracts;

#[cfg(feature = "contracts")]
mod macros {
    /// A pre-condition of a function or trait item
    pub use creusot_contracts_proc::requires;

    /// A post-condition of a function or trait item
    pub use creusot_contracts_proc::ensures;

    pub use creusot_contracts_proc::ghost;

    /// A loop invariant
    /// The first argument should be a name for the invariant
    /// The second argument is the Pearlite expression for the loop invariant
    pub use creusot_contracts_proc::invariant;

    /// Declares a trait item as being a law which is autoloaded as soon another
    /// trait item is used in a function
    pub use creusot_contracts_proc::law;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs as it is *ghost*, in exchange it can
    /// use logical operations and syntax with the help of the [pearlite] macro.
    pub use creusot_contracts_proc::logic;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs as it is *ghost*, in exchange it can
    /// use logical operations and syntax with the help of the [pearlite] macro.
    pub use creusot_contracts_proc::predicate;

    /// Inserts a *logical* assertion into the code. This assertion will not be checked at runtime
    /// but only during proofs. However, it has access to the ghost context and can use logical operations
    /// and syntax.
    pub use creusot_contracts_proc::proof_assert;

    /// Instructs Pearlite to ignore the body of a declaration, assuming any contract the declaration has is
    /// valid.
    pub use creusot_contracts_proc::trusted;

    /// Declares a variant for a function, this is primarily used in combination with logical functions
    /// The variant must be an expression which returns a type implementing [WellFounded]
    pub use creusot_contracts_proc::variant;

    /// Enables Pearlite syntax, granting access to Pearlite specific operators and syntax
    pub use creusot_contracts_proc::pearlite;

    /// Allows specifications to be attached to functions coming from external crates
    /// TODO: Document syntax
    pub use creusot_contracts_proc::extern_spec;

    /// Allows specifying both a pre- and post-condition in a single statement.
    /// Expects an expression in either the form of a method or function call
    /// Arguments to the call can be prefixed with `mut` to indicate that they are mutable borrows.
    ///
    /// Generates a `requires` and `ensures` clause in the shape of the input expression, with
    /// `mut` replaced by `*` in the `requires` and `^` in the ensures.
    pub use creusot_contracts_proc::maintains;
}

#[cfg(not(feature = "contracts"))]
mod macros {
    /// A pre-condition of a function or trait item
    pub use creusot_contracts_dummy::requires;

    /// A post-condition of a function or trait item
    pub use creusot_contracts_dummy::ensures;

    pub use creusot_contracts_dummy::ghost;

    /// A loop invariant
    /// The first argument should be a name for the invariant
    /// The second argument is the Pearlite expression for the loop invariant
    pub use creusot_contracts_dummy::invariant;

    /// Declares a trait item as being a law which is autoloaded as soon another
    /// trait item is used in a function
    pub use creusot_contracts_dummy::law;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs as it is *ghost*, in exchange it can
    /// use logical operations and syntax with the help of the [pearlite] macro.
    pub use creusot_contracts_dummy::logic;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs as it is *ghost*, in exchange it can
    /// use logical operations and syntax with the help of the [pearlite] macro.
    pub use creusot_contracts_dummy::predicate;

    /// Inserts a *logical* assertion into the code. This assertion will not be checked at runtime
    /// but only during proofs. However, it has access to the ghost context and can use logical operations
    /// and syntax.
    pub use creusot_contracts_dummy::proof_assert;

    /// Instructs Pearlite to ignore the body of a declaration, assuming any contract the declaration has is
    /// valid.
    pub use creusot_contracts_dummy::trusted;

    /// Declares a variant for a function, this is primarily used in combination with logical functions
    /// The variant must be an expression which returns a type implementing [WellFounded]
    pub use creusot_contracts_dummy::variant;

    /// Enables Pearlite syntax, granting access to Pearlite specific operators and syntax
    pub use creusot_contracts_dummy::pearlite;

    /// Allows specifications to be attached to functions coming from external crates
    /// TODO: Document syntax
    pub use creusot_contracts_dummy::extern_spec;

    /// Allows specifying both a pre- and post-condition in a single statement.
    /// Expects an expression in either the form of a method or function call
    /// Arguments to the call can be prefixed with `mut` to indicate that they are mutable borrows.
    ///
    /// Generates a `requires` and `ensures` clause in the shape of the input expression, with
    /// `mut` replaced by `*` in the `requires` and `^` in the ensures.
    pub use creusot_contracts_dummy::maintains;
}

#[cfg(feature = "contracts")]
#[path = "stubs.rs"]
pub mod __stubs;

pub mod logic;

#[cfg_attr(not(feature = "contracts"), allow(unused))]
pub mod std;

#[cfg(feature = "contracts")]
pub mod ghost;

#[cfg(not(feature = "contracts"))]
pub mod ghost {
    pub struct Ghost<T>(std::marker::PhantomData<T>)
    where
        T: ?Sized;

    impl<T> Ghost<T> {
        pub fn new() -> Ghost<T> {
            Ghost(std::marker::PhantomData)
        }
    }
}

pub mod invariant;
pub mod model;
pub mod resolve;
pub mod well_founded;

// We add some common things at the root of the creusot-contracts library
pub use crate::{
    ghost::Ghost,
    logic::{Int, OrdLogic, Seq},
    macros::*,
    model::{DeepModel, ShallowModel},
    resolve::Resolve,
    std::{
        // Shadow std::prelude by our version.
        // For Clone and PartialEq, this is important for the derive macro.
        // If the user write the glob pattern "use creusot_contracts::*", then
        // rustc will either shadow the old identifier or complain about the
        // ambiguïty (ex: for the derive macros Clone and PartialEq, a glob
        // pattern is not enough to force rustc to use our version, but at least
        // we get an error message).
        clone::Clone,
        cmp::PartialEq,
        default::Default,
        iter::{FromIterator, IntoIterator, Iterator},
    },
    well_founded::WellFounded,
};

// Export extension traits anonymously
pub use crate::std::{
    iter::{SkipExt as _, TakeExt as _},
    ops::{FnExt as _, FnMutExt as _, FnOnceExt as _, RangeInclusiveExt as _},
    slice::SliceExt as _,
};
