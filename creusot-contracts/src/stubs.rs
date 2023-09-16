use crate as creusot_contracts;
use creusot_contracts::{logic, open};

#[creusot::no_translate]
#[rustc_diagnostic_item = "fin"]
pub fn fin<T: ?Sized>(_: &mut T) -> Box<T> {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "equal"]
pub fn equal<T: ?Sized>(_: T, _: T) -> bool {
    panic!();
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "neq"]
pub fn neq<T: ?Sized>(_: T, _: T) -> bool {
    panic!();
}

// FIXME : T should be ?Sized
#[creusot::no_translate]
#[rustc_diagnostic_item = "exists"]
pub fn exists<T, F: Fn(T) -> bool>(_: F) -> bool {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "forall"]
pub fn forall<T, F: Fn(T) -> bool>(_: F) -> bool {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "implication"]
pub fn implication(_: bool, _: bool) -> bool {
    panic!();
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "old"]
pub fn old<T: ?Sized>(_: T) -> Box<T> {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "absurd"]
pub fn abs<T: ?Sized>() -> Box<T> {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "variant_check"]
pub fn variant_check<R: crate::well_founded::WellFounded + ?Sized>(_: R) -> Box<R> {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "closure_result_constraint"]
pub fn closure_result<R: ?Sized>(_: R, _: R) {}

#[creusot::no_translate]
#[rustc_diagnostic_item = "ghost_from_fn"]
pub fn ghost_from_fn<T: ?Sized, F: Fn() -> crate::Ghost<T>>(_: F) -> crate::Ghost<T> {
    panic!()
}

#[creusot::no_translate]
#[creusot::builtins = "prelude.Mapping.from_fn"]
pub fn mapping_from_fn<A, B, F: FnOnce(A) -> B>(_: F) -> crate::logic::Mapping<A, B> {
    panic!()
}

#[logic] // avoid triggering error since this is prusti specific
#[open]
#[creusot::no_translate]
#[rustc_diagnostic_item = "prusti_curr"]
pub fn curr<T>(_: T) -> T {
    absurd
}

#[logic] // avoid triggering error since this is prusti specific
#[open]
#[creusot::no_translate]
#[rustc_diagnostic_item = "prusti_expiry"]
pub fn at_expiry<'a: 'a, T>(_: T) -> T {
    absurd
}

pub trait ReplaceLifetimesWithStatic {
    #[rustc_diagnostic_item = "prusti_replace_static_user"]
    type WithStatic;
}

impl<T> ReplaceLifetimesWithStatic for T {
    // this is true modulo lifetimes
    type WithStatic = T;
}

pub type WithStatic<T> = <T as ReplaceLifetimesWithStatic>::WithStatic;

pub mod __static {

    /// Internal use only
    #[rustc_diagnostic_item = "prusti_replace_lft"]
    pub struct ReplaceLft<'x, T>(T, &'x ());
}

#[logic]
#[open]
#[creusot::prusti::home_sig = "('curr) -> 'x"]
/// Hypothetical snapshot function that duplicates t so that it can be used anywhere
/// Note: dereferencing a mutable reference created by a snapshot uses the current operator
pub fn snap<T>(t: T) -> WithStatic<T> {
    t
}

#[logic] // avoid triggering error since this is prusti specific
#[open]
#[creusot::no_translate]
#[rustc_diagnostic_item = "prusti_dbg_ty"]
pub fn __dbg_ty<T>(_: T) -> T {
    absurd
}
