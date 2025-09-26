#![cfg_attr(
    feature = "creusot",
    feature(
        box_patterns,
        extend_one,
        hash_set_entry,
        if_let_guard,
        proc_macro_def_site,
        proc_macro_diagnostic,
        proc_macro_span,
    )
)]

use proc_macro::TokenStream as TS1;

pub(crate) mod common;
mod ghost;

/// Macro implementations used by `cargo creusot`.
#[cfg(feature = "creusot")]
mod creusot;

#[cfg(creusot)]
use creusot as c;

/// Macro implementations used by `cargo build`.
#[cfg(not(creusot))]
mod dummy;

#[cfg(not(creusot))]
use dummy as c;

/// For rust-analyzer, we set `cfg(feature = "creusot")` to be able to check
/// `crate::creusot`, but it is not used (`cfg(creusot)` is still false).
/// This macro avoids warnings by faking dependencies on the functions from `crate::creusot`.
macro_rules! allow_unused {
    ($($name:ident)::+) => {
        #[cfg(all(not(creusot), feature = "creusot"))]
        #[allow(unused)]
        use $($name)::+ as _;
    };
}

macro_rules! proc_macro_attributes {
    ($($name:ident)+) => {
        $(#[proc_macro_attribute]
        pub fn $name(attr: TS1, tokens: TS1) -> TS1 {
            allow_unused!(creusot::$name);
            c::$name(attr, tokens)
        })+
    };
}

proc_macro_attributes! {
    requires
    ensures
    invariant
    variant
    check
    logic
    trusted
    opaque
    builtin
    intrinsic
    open_inv_result
    bitwise_proof
    maintains
    erasure
}

macro_rules! proc_macros {
    ($($name:ident)+) => {
        $(#[proc_macro]
        pub fn $name(tokens: TS1) -> TS1 {
            allow_unused!(creusot::$name);
            c::$name(tokens)
        })+
    };
}

proc_macros! {
    proof_assert
    snapshot
    ghost
    ghost_let
    pearlite
    extern_spec
    declare_namespace
}

#[proc_macro_derive(DeepModel, attributes(DeepModelTy))]
pub fn derive_deep_model(tokens: TS1) -> TS1 {
    allow_unused!(creusot::derive_deep_model);
    c::derive_deep_model(tokens)
}

#[proc_macro_derive(Resolve)]
pub fn derive_resolve(tokens: TS1) -> TS1 {
    allow_unused!(creusot::derive_resolve);
    c::derive_resolve(tokens)
}

#[cfg(feature = "creusot")]
#[proc_macro_derive(Clone)]
pub fn derive_clone(tokens: TS1) -> TS1 {
    creusot::derive_clone(tokens)
}

#[cfg(feature = "creusot")]
#[proc_macro_derive(Default, attributes(default))]
pub fn derive_default(tokens: TS1) -> TS1 {
    creusot::derive_default(tokens)
}

#[cfg(feature = "creusot")]
#[proc_macro_derive(PartialEq)]
pub fn derive_partial_eq(tokens: TS1) -> TS1 {
    creusot::derive_partial_eq(tokens)
}
