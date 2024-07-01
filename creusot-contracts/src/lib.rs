#![cfg_attr(
    creusot,
    feature(unsized_locals, fn_traits, min_specialization),
    allow(incomplete_features),
    feature(slice_take),
    feature(print_internals, fmt_internals, fmt_helpers_for_derive)
)]
#![cfg_attr(feature = "typechecker", feature(rustc_private), feature(box_patterns))]
#![feature(
    step_trait,
    allocator_api,
    unboxed_closures,
    tuple_trait,
    strict_provenance,
    panic_internals,
    libstd_sys_internals,
    rt
)]
#![cfg_attr(not(creusot), feature(rustc_attrs))]
#![cfg_attr(not(creusot), allow(internal_features))]

extern crate self as creusot_contracts;

#[cfg(creusot)]
extern crate creusot_contracts_proc as base_macros;

#[cfg(not(creusot))]
extern crate creusot_contracts_dummy as base_macros;

mod macros {
    /// A pre-condition of a function or trait item
    pub use base_macros::requires;

    /// A post-condition of a function or trait item
    pub use base_macros::ensures;

    pub use base_macros::snapshot;

    /// Opens a 'ghost block'.
    ///
    /// Ghost blocks are used to execute ghost code: code that will be erased in the
    /// normal execution of the program, but could influence the proof.
    ///
    /// Note that ghost blocks are subject to some constraints, that ensure the behavior
    /// of the code stays the same with and without ghost blocks:
    /// - They may not contain code that crashes or runs indefinitely. In other words,
    /// they can only call [`pure`] functions.
    /// - All variables that enter the ghost blocks must either be [`Copy`], or a
    ///  [`GhostBox`](crate::ghost::GhostBox).
    /// - The variable returned by the ghost block must be of type `()` or
    /// [`GhostBox`](crate::ghost::GhostBox).
    pub use base_macros::ghost;

    /// Shorthand for `ghost!{ GhostBox::new(...) }`.
    pub use base_macros::gh;

    /// Indicate that the function terminates: fullfilling the `requires` clauses
    /// ensures that this function will not loop indefinitively.
    pub use base_macros::terminates;

    /// Indicate that the function is pure: fullfilling the `requires` clauses ensures
    /// that this function will terminate, and will not panic.
    ///
    /// # No panics ?
    ///
    /// "But I though Creusot was supposed to check the absence of panics ?"
    ///
    /// That's true, but with a caveat: some functions of the standart library are
    /// allowed to panic in specific cases. The main example is `Vec::push`: we want its
    /// specification to be
    /// ```ignore
    /// #[ensures((^self)@ == self@.push(v))]
    /// fn push(&mut self, v: T) { /* ... */ }
    /// ```
    ///
    /// But the length of a vector [cannot overflow `isize::MAX`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push).
    /// This is a very annoying condition to require, so we don't.
    /// In exchange, this means `Vec::push` might panic in some cases, even though your
    /// code passed Creusot's verification.
    ///
    /// # Non-pure std function
    ///
    /// Here are some examples of functions in `std` that are not marked as terminates
    /// but not pure (this list might not be exhaustive):
    /// - `Vec::push`, `Vec::insert`, `Vec::reserve`, `Vec::with_capacity`
    /// - `str::to_string`
    /// - `<&[T]>::into_vec`
    /// - `Deque::push_front`, `Deque::push_back`, `Deque::with_capacity`
    pub use base_macros::pure;

    /// A loop invariant
    /// The first argument should be a name for the invariant
    /// The second argument is the Pearlite expression for the loop invariant
    pub use base_macros::invariant;

    /// Declares a trait item as being a law which is autoloaded as soon another
    /// trait item is used in a function
    pub use base_macros::law;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs, but in exchange it can use logical
    /// operations and syntax with the help of the [`pearlite!`] macro.
    ///
    /// # `prophetic`
    ///
    /// If you wish to use the `^` operator on mutable borrows to get the final value, you need to
    /// specify that the function is _prophetic_, like so:
    /// ```ignore
    /// #[logic(prophetic)]
    /// fn uses_prophecies(x: &mut Int) -> Int {
    ///     pearlite! { if ^x == 0 { 0 } else { 1 } }
    /// }
    /// ```
    /// Such a logic function cannot be used in [`snapshot!`] anymore, and cannot be
    /// called from a regular [`logic`] or [`predicate`] function.
    pub use base_macros::logic;

    /// Declare a function as being a logical function, this declaration must be pure and
    /// total. It cannot be called from Rust programs as it is *ghost*, in exchange it can
    /// use logical operations and syntax with the help of the [`pearlite!`] macro.
    ///
    /// It **must** return a boolean.
    ///
    /// # `prophetic`
    ///
    /// If you wish to use the `^` operator on mutable borrows to get the final value, you need to
    /// specify that the function is _prophetic_, like so:
    /// ```ignore
    /// #[predicate(prophetic)]
    /// fn uses_prophecies(x: &mut Int) -> bool {
    ///     pearlite! { ^x == 0 }
    /// }
    /// ```
    /// Such a predicate function cannot be used in [`snapshot!`] anymore, and cannot be
    /// called from a regular [`logic`] or [`predicate`] function.
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

    /// Allows the body of a logical definition to be made visible to provers. An optional visibility modifier can be
    /// provided to restrict the context in whcih the obdy is opened.
    /// By default, bodies are *opaque*: they are only visible to definitions in the same module (like `pub(self)` for visibility).
    ///
    /// A body can only be visible in contexts where all the symbols used in the body are also visible.
    /// This means you cannot `#[open]` a body which refers to a `pub(crate)` symbol.
    pub use base_macros::open;
}

#[cfg(creusot)]
#[path = "stubs.rs"]
pub mod __stubs;

pub mod logic;

#[cfg_attr(not(creusot), allow(unused))]
pub mod std;

#[cfg(creusot)]
pub mod num_rational;

#[cfg(creusot)]
pub mod ghost;

#[cfg(creusot)]
pub mod snapshot;

#[cfg(not(creusot))]
pub mod ghost {
    pub struct GhostBox<T>(std::marker::PhantomData<T>)
    where
        T: ?Sized;

    impl<T: ?Sized> GhostBox<T> {
        pub fn from_fn(_: fn() -> T) -> Self {
            GhostBox(std::marker::PhantomData)
        }
    }

    impl<T: ?Sized> Clone for GhostBox<T> {
        fn clone(&self) -> Self {
            GhostBox(std::marker::PhantomData)
        }
    }

    impl<T: ?Sized> Copy for GhostBox<T> {}

    impl<T: ?Sized> GhostBox<T> {
        pub fn uninit() -> Self {
            Self(std::marker::PhantomData)
        }
    }
}

#[cfg(not(creusot))]
pub mod snapshot {
    pub struct Snapshot<T>(std::marker::PhantomData<T>)
    where
        T: ?Sized;

    impl<T: ?Sized> Snapshot<T> {
        pub fn from_fn(_: fn() -> T) -> Self {
            Snapshot(std::marker::PhantomData)
        }
    }

    impl<T: ?Sized> Clone for Snapshot<T> {
        fn clone(&self) -> Self {
            Snapshot(std::marker::PhantomData)
        }
    }

    impl<T: ?Sized> Copy for Snapshot<T> {}
}

pub mod ghost_ptr;
pub mod invariant;
pub mod model;
pub mod resolve;
pub mod util;
pub mod well_founded;

// We add some common things at the root of the creusot-contracts library
mod base_prelude {
    pub use crate::{
        ghost::GhostBox,
        logic::{IndexLogic as _, Int, OrdLogic, Seq},
        model::{DeepModel, ShallowModel},
        resolve::Resolve,
        snapshot::Snapshot,
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
}
pub mod prelude {
    pub use crate::{base_prelude::*, macros::*};
}

pub use prelude::*;

// The std vec macro uses special magic to construct the array argument
// to Box::new directly on the heap. Because the generated MIR is hard
// to translate, we provide a custom vec macro which does not do this.
#[macro_export]
macro_rules! vec {
    () => (
        ::std::vec::Vec::new()
    );
    ($elem:expr; $n:expr) => (
        ::std::vec::from_elem($elem, $n)
    );
    ($($x:expr),*) => (
        <[_]>::into_vec(::std::boxed::Box::new([$($x),*]))
    );
    ($($x:expr,)*) => (vec![$($x),*])
}
