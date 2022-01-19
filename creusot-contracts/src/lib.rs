#![cfg_attr(feature = "contracts", feature(unsized_fn_params))]
#![cfg_attr(feature = "typechecker", feature(rustc_private), feature(box_patterns, box_syntax))]

// with_unique_ident! {( $my_ns:unique_ident ) => (
//     #[doc(hidden)]
//     #[macro_export]
//     macro_rules! __custom_namespaced__ {( $item:item ) => (
//         #[$crate::custom_namespace($my_ns)]
//         $item
//     )}
// )}

#[cfg(feature = "contracts")]
mod macros {
    /// A pre-condition of a function or trait item
    pub use creusot_contracts_proc::requires;

    /// A post-condition of a function or trait item
    pub use creusot_contracts_proc::ensures;

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
}

#[cfg(not(feature = "contracts"))]
mod macros {
    /// A pre-condition of a function or trait item
    pub use creusot_contracts_dummy::requires;

    /// A post-condition of a function or trait item
    pub use creusot_contracts_dummy::ensures;

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
    pub use creusot_contracts_proc::pearlite;

    /// Allows specifications to be attached to functions coming from external crates
    /// TODO: Document syntax
    pub use creusot_contracts_proc::extern_spec;
}

pub use macros::*;

#[cfg(feature = "contracts")]
pub mod stubs;

#[cfg(feature = "contracts")]
pub mod logic;

#[cfg(feature = "contracts")]
pub mod std;

#[cfg(not(feature = "contracts"))]
pub mod std {
    pub use std::vec;
}

#[cfg(not(feature = "contracts"))]
pub mod logic {
    pub struct Ghost<T>(std::marker::PhantomData<T>)
    where
        T: ?Sized;

    impl<T> Ghost<T> {
        pub fn record(_: &T) -> Ghost<T> {
            Ghost(std::marker::PhantomData)
        }
    }
}

pub use logic::*;

// Re-export the rand crate
pub use rand;
