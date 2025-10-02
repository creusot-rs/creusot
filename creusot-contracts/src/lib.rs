//! The "standard library" of Creusot.
//!
//! To start using Creusot, you should always import that crate. The recommended way is
//! to have a glob import:
//!
//! ```
//! use creusot_contracts::*;
//! ```
//!
//! # Writing specifications
//!
//! To start writing specification, use the [`requires`] and [`ensures`] macros:
//!
//! ```
//! use creusot_contracts::*;
//!
//! #[requires(x < i32::MAX)]
//! #[ensures(result@ == x@ + 1)]
//! fn add_one(x: i32) -> i32 {
//!     x + 1
//! }
//! ```
//!
//! For a more detailed explanation, see the [guide](https://creusot-rs.github.io/creusot/guide).
//!
//! # Module organization
//!
//! 1. Core features of Creusot
//!
//!     - [`invariant`][mod@invariant]: Type invariants
//!     - [`macros`]: `#[requires]`, `#[ensures]`, etc.
//!     - [`resolve`][mod@resolve]: Resolve mutable borrows
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
//! 6. [`prelude`][mod@prelude]: What you get from `use creusot_contracts::*;`
#![cfg_attr(
    feature = "nightly",
    allow(incomplete_features, internal_features),
    feature(
        core_intrinsics,
        const_destruct,
        fn_traits,
        print_internals,
        fmt_internals,
        fmt_helpers_for_derive,
        step_trait,
        try_trait_v2,
        allocator_api,
        unboxed_closures,
        tuple_trait,
        panic_internals,
        libstd_sys_internals,
        rt,
        never_type,
        ptr_metadata,
        hint_must_use,
        pointer_is_aligned_to,
        edition_panic,
    )
)]

extern crate creusot_contracts_proc as base_macros;
extern crate self as creusot_contracts;

/// Specification are written using these macros
///
/// All of those are re-exported at the top of the crate.
pub mod macros {
    /// A pre-condition of a function or trait item
    ///
    /// The inside of a `requires` may look like Rust code, but it is in fact
    /// [pearlite](https://creusot-rs.github.io/creusot/guide/pearlite).
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[requires(x@ == 1)]
    /// fn foo(x: i32) {}
    /// ```
    pub use base_macros::requires;

    /// A post-condition of a function or trait item
    ///
    /// The inside of a `ensures` may look like Rust code, but it is in fact
    /// [pearlite](https://creusot-rs.github.io/creusot/guide/pearlite).
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[ensures(result@ == 1)]
    /// fn foo() -> i32 { 1 }
    /// ```
    pub use base_macros::ensures;

    /// Create a new [`Snapshot`](crate::Snapshot) object.
    ///
    /// The inside of `snapshot` may look like Rust code, but it is in fact
    /// [pearlite](https://creusot-rs.github.io/creusot/guide/pearlite).
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let mut x = 1;
    /// let s = snapshot!(x);
    /// x = 2;
    /// proof_assert!(*s == 1i32);
    /// ```
    ///
    /// # `snapshot!` and ownership
    ///
    /// Snapshots are used to talk about the logical value of an object, and as such
    /// they carry no ownership. This means that code like this is perfectly fine:
    ///
    /// ```
    /// # use creusot_contracts::{*, vec};
    /// let v: Vec<i32> = vec![1, 2];
    /// let s = snapshot!(v);
    /// assert!(v[0] == 1); // ok, `s` does not have ownership of `v`
    /// drop(v);
    /// proof_assert!(s[0] == 1i32); // also ok!
    /// ```
    pub use base_macros::snapshot;

    /// Opens a 'ghost block'.
    ///
    /// Ghost blocks are used to execute ghost code: code that will be erased in the
    /// normal execution of the program, but could influence the proof.
    ///
    /// Note that ghost blocks are subject to some constraints, that ensure the behavior
    /// of the code stays the same with and without ghost blocks:
    /// - They may not contain code that crashes or runs indefinitely. In other words,
    ///   they can only call [`check(ghost)`][check#checkghost] functions.
    /// - All variables that are read in the ghost block must either be [`Copy`], or a
    ///   [`Ghost`].
    /// - All variables that are modified in the ghost block must be [`Ghost`]s.
    /// - The variable returned by the ghost block will automatically be wrapped in a
    ///   [`Ghost`].
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// let x = 1;
    /// let mut g = ghost!(Seq::new()); // g is a zero-sized variable at runtime
    /// ghost! {
    ///     g.push_back_ghost(x);
    /// };
    /// ```
    ///
    /// [`Ghost`]: crate::ghost::Ghost
    pub use base_macros::ghost;

    pub use base_macros::ghost_let;

    /// Specify that the function can be called in additionnal contexts.
    ///
    /// # Syntax
    ///
    /// Checking modes are specified as arguments:
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[check(terminates)]
    /// fn foo() { /* */ }
    ///
    /// #[check(ghost)]
    /// fn bar() { /* */ }
    ///
    /// // cannot be called in neither ghost nor terminates contexts
    /// fn baz() { /* */ }
    /// ```
    ///
    /// # `#[check(terminates)]`
    ///
    /// The function is guaranteed to terminate.
    ///
    /// At this moment, this means that:
    /// - the function cannot be recursive
    /// - the function cannot contain loops
    /// - the function can only call other `terminates` or `ghost` functions.
    ///
    /// The first two limitations may be lifted at some point.
    ///
    /// # `#[check(ghost)]`
    ///
    /// The function can be called from ghost code. In particular, this means
    /// that the fuction will not panic.
    ///
    /// # No panics ?
    ///
    /// "But I though Creusot was supposed to check the absence of panics ?"
    ///
    /// That's true, but with a caveat: some functions of the standard library
    /// are allowed to panic in specific cases. The main example is `Vec::push`:
    /// we want its specification to be
    /// ```ignore
    /// #[ensures((^self)@ == self@.push(v))]
    /// fn push(&mut self, v: T) { /* ... */ }
    /// ```
    ///
    /// But the length of a vector [cannot overflow `isize::MAX`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push).
    /// This is a very annoying condition to check, so we don't. In exchange,
    /// this means `Vec::push` might panic in some cases, even though your
    /// code passed Creusot's verification.
    ///
    /// # Non-ghost std function
    ///
    /// Here are some examples of functions in `std` that are not marked as
    /// `terminates` but not `ghost` (this list is not exhaustive):
    /// - `Vec::push`, `Vec::insert`, `Vec::reserve`, `Vec::with_capacity`
    /// - `str::to_string`
    /// - `<&[T]>::into_vec`
    /// - `Deque::push_front`, `Deque::push_back`, `Deque::with_capacity`
    pub use base_macros::check;

    /// A loop invariant
    ///
    /// The inside of a `invariant` may look like Rust code, but it is in fact
    /// [pearlite](https://creusot-rs.github.io/creusot/guide/pearlite).
    ///
    /// # Produced
    ///
    /// If the loop is a `for` loop, you have access to a special variable `produced`, that
    /// holds a [sequence](crate::Seq) of all the (logical representations of) items the
    /// iterator yielded so far.
    ///
    /// # Example
    ///
    /// ```ignore
    /// # use creusot_contracts::*;
    /// let mut v = Vec::new();
    /// #[invariant(v@.len() == produced.len())]
    /// #[invariant(forall<j> 0 <= j && j < produced.len() ==> v@[j]@ == j)]
    /// for i in 0..10 {
    ///     v.push(i);
    /// }
    /// ```
    pub use base_macros::invariant;

    /// Declare a function as being a logical function
    ///
    /// This declaration must be pure and total. It cannot be called from Rust programs,
    /// but in exchange it can use logical operations and syntax with the help of the
    /// [`pearlite!`] macro.
    ///
    /// # `open`
    ///
    /// Allows the body of a logical definition to be made visible to provers
    ///
    /// By default, bodies are *opaque*: they are only visible to definitions in the same
    /// module (like `pub(self)` for visibility).
    /// An optional visibility modifier can be provided to restrict the context in which
    /// the body is opened.
    ///
    /// A body can only be visible in contexts where all the symbols used in the body are also visible.
    /// This means you cannot open a body which refers to a `pub(crate)` symbol.
    ///
    /// # Example
    ///
    /// ```
    /// mod inner {
    ///     use creusot_contracts::*;
    ///     #[logic]
    ///     #[ensures(result == x + 1)]
    ///     pub(super) fn foo(x: Int) -> Int {
    ///         // ...
    /// # x + 1
    ///     }
    ///
    ///     #[logic(open)]
    ///     pub(super) fn bar(x: Int) -> Int {
    ///         x + 1
    ///     }
    /// }
    ///
    /// // The body of `foo` is not visible here, only the `ensures`.
    /// // But the whole body of `bar` is visible
    /// ```
    ///
    /// # `prophetic`
    ///
    /// If you wish to use the `^` operator on mutable borrows to get the final value, you need to
    /// specify that the function is _prophetic_, like so:
    /// ```
    /// # use creusot_contracts::*;
    /// #[logic(prophetic)]
    /// fn uses_prophecies(x: &mut Int) -> Int {
    ///     pearlite! { if ^x == 0 { 0 } else { 1 } }
    /// }
    /// ```
    /// Such a logic function cannot be used in [`snapshot!`] anymore, and cannot be
    /// called from a regular [`logic`] function.
    ///
    /// # law
    ///
    /// Declares a trait item as being a law which is autoloaded as soon another
    /// trait item is used in a function.
    ///
    /// ```ignore
    /// trait CommutativeOp {
    ///     fn op(self, other: Self) -> Int;
    ///
    ///     #[logic(law)]
    ///     #[ensures(forall<x: Self, y: Self> x.op(y) == y.op(x))]
    ///     fn commutative();
    /// }
    /// ```
    pub use base_macros::logic;

    /// Inserts a *logical* assertion into the code
    ///
    /// This assertion will not be checked at runtime but only during proofs. However,
    /// it can use [pearlite](https://creusot-rs.github.io/creusot/guide/pearlite) syntax.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::{*, vec};
    /// let x = 1;
    /// let v = vec![x, 2];
    /// let s = snapshot!(v);
    /// proof_assert!(s[0] == 1i32);
    /// ```
    pub use base_macros::proof_assert;

    /// Makes a logical definition or a type declaration opaque, meaning that users of this declaration will not see
    /// its definition.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[opaque]
    /// struct Opaque(()); // This will is an abstract type
    ///
    /// #[logic]
    /// #[opaque] // Synonym: #[logic(opaque)]
    /// fn foo() -> i32 { // This is an uninterpreted logic function
    ///     dead
    /// }
    /// ```
    pub use base_macros::opaque;

    /// Instructs Creusot to not emit any VC for a declaration, assuming any contract the declaration has is
    /// valid.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[trusted] // this is too hard to prove :(
    /// #[ensures(result@ == 1)]
    /// fn foo() -> i32 {
    ///     // complicated code...
    /// # 1
    /// }
    /// ```
    ///
    /// These declarations are part of the trusted computing base (TCB). You should strive to use
    /// this as little as possible.
    pub use base_macros::trusted;

    /// Declares a variant for a function or a loop.
    ///
    /// This is primarily used in combination with recursive logical functions.
    ///
    /// The variant must be an expression whose type implements
    /// [`WellFounded`](crate::logic::WellFounded).
    ///
    /// # Example
    ///
    /// - Recursive logical function:
    /// ```
    /// # use creusot_contracts::*;
    /// #[logic]
    /// #[variant(x)]
    /// #[requires(x >= 0)]
    /// fn recursive_add(x: Int, y: Int) -> Int {
    ///     if x == 0 {
    ///         y
    ///     } else {
    ///         recursive_add(x - 1, y + 1)
    ///     }
    /// }
    /// ```
    /// - Loop variant:
    /// ```
    /// # use creusot_contracts::*;
    /// #[check(terminates)]
    /// #[ensures(result == x)]
    /// fn inneficient_identity(mut x: i32) -> i32 {
    ///     let mut res = 0;
    ///     let total = snapshot!(x);
    ///     // Attribute on loop are experimental in Rust, just pretend the next 2 lines are uncommented :)
    ///     // #[variant(x)]
    ///     // #[invariant(x@ + res@ == total@)]
    ///     while x > 0 {
    ///         x -= 1;
    ///         res += 1;
    ///     }
    ///     res
    /// }
    /// ```
    pub use base_macros::variant;

    /// Enables [pearlite](https://creusot-rs.github.io/creusot/guide/pearlite) syntax, granting access to Pearlite specific operators and syntax
    ///
    /// This is meant to be used in [`logic`] functions.
    ///
    /// # Example
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[logic]
    /// fn all_ones(s: Seq<Int>) -> bool {
    ///     // Allow access to `forall` and `==>` among other things
    ///     pearlite! {
    ///         forall<i> 0 <= i && i < s.len() ==> s[i] == 1
    ///     }
    /// }
    /// ```
    pub use base_macros::pearlite;

    /// Allows specifications to be attached to functions coming from external crates
    ///
    /// TODO: Document syntax
    pub use base_macros::extern_spec;

    /// Allows specifying both a pre- and post-condition in a single statement.
    ///
    /// Expects an expression in either the form of a method or function call
    /// Arguments to the call can be prefixed with `mut` to indicate that they are mutable borrows.
    ///
    /// Generates a `requires` and `ensures` clause in the shape of the input expression, with
    /// `mut` replaced by `*` in the `requires` and `^` in the ensures.
    pub use base_macros::maintains;

    /// This attribute can be used on a function or closure to instruct Creusot not to ensure as a postcondition that the
    /// return value of the function satisfies its [type invariant](crate::Invariant).
    pub use base_macros::open_inv_result;

    /// This attribute indicates that the function need to be proved in "bitwise" mode, which means that Creusot will use
    /// the bitvector theory of SMT solvers.
    pub use base_macros::bitwise_proof;

    /// This attribute indicates that a logic function or a type should be translated to a specific type in Why3.
    pub use base_macros::builtin;

    /// Check that the annotated function erases to another function.
    ///
    /// See the [guide: Erasure check](https://creusot-rs.github.io/creusot/guide/erasure.html).
    ///
    /// # Usage
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// #[erasure(f)]
    /// fn g(x: usize, i: Ghost<Int>) { /* ... */ }
    ///
    /// #[erasure(private crate_name::full::path::to::f2)]
    /// fn g2(y: bool) { /* ... */ }
    /// ```
    ///
    /// # Inside `extern_spec!`
    ///
    /// The shorter `#[erasure]` (without argument) can be used in `extern_spec!` to check
    /// that the annotated function body matches the original one.
    ///
    /// ```
    /// # use creusot_contracts::*;
    /// extern_spec! {
    ///   #[erasure]
    ///   fn some_external_function() { /* ... */ }
    /// }
    /// ```
    pub use base_macros::erasure;

    pub(crate) use base_macros::intrinsic;

    /// Defines a _logical alias_ for a program function.
    ///
    /// Logical aliases allow you to use the same name for a program and a [`logic`] function.
    /// Creusot will generate a proof obligation to show that the two functions return
    /// the same results.
    ///
    /// # Example
    ///
    /// ```rust
    /// use creusot_contracts::*;
    /// pub struct S<T> {
    ///     t: T,
    /// }
    /// impl<T> S<T> {
    ///     #[has_logical_alias(Self::read_t_logic)]
    ///     pub fn read_t(&self) -> &T {
    ///         &self.t
    ///     }
    ///
    ///     #[logic]
    ///     pub fn read_t_logic(&self) -> &T {
    ///         &self.t
    ///     }
    /// }
    ///
    /// // ...
    ///
    /// #[requires(s.read_t().view() == 1)]
    /// pub fn foo(s: S<i32>) { /* ... */ }
    /// ```
    pub use base_macros::has_logical_alias;
}

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
#[cfg_attr(not(creusot), allow(unused))]
pub mod std;

// We add some common things at the root of the creusot-contracts library
mod base_prelude {
    pub use crate::{
        ghost::Ghost,
        invariant::Invariant,
        logic::{Int, OrdLogic, Seq, ops::IndexLogic as _},
        model::{DeepModel, View},
        resolve::Resolve,
        snapshot::Snapshot,
        std::{
            // Shadow std::prelude by our version.
            // For Clone, Default and PartialEq, this is important for the derive macro.
            // If the user write the glob pattern "use creusot_contracts::*", then
            // rustc will either shadow the old identifier or complain about the
            // ambiguity (ex: for the derive macros Clone and PartialEq, a glob
            // pattern is not enough to force rustc to use our version, but at least
            // we get an error message).
            clone::Clone,
            cmp::PartialEq,
            default::Default,
            iter::{FromIterator, Iterator},
        },
    };

    // Export extension traits anonymously
    pub use crate::std::{
        char::CharExt as _,
        iter::{SkipExt as _, TakeExt as _},
        ops::{FnExt as _, FnMutExt as _, FnOnceExt as _, RangeInclusiveExt as _},
        option::OptionExt as _,
        ptr::PointerExt as _,
        slice::SliceExt as _,
    };

    #[cfg(creusot)]
    pub use crate::{invariant::inv, resolve::resolve};
}
/// Re-exports available under the `creusot_contracts` namespace
pub mod prelude {
    pub use crate::{base_prelude::*, macros::*};
}

pub use prelude::*;

/// Creusot-friendly replacement of `vec!`
///
/// The std vec macro uses special magic to construct the array argument
/// to `Box::new` directly on the heap. Because the generated MIR is hard
/// to translate, we provide a custom `vec!` macro which does not do this.
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
