use crate as creusot_contracts;
use creusot_contracts::{ghost, open, trusted};

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

#[ghost] // avoid triggering error since this is prusti specific
#[open]
#[creusot::no_translate]
#[rustc_diagnostic_item = "prusti_curr"]
pub fn curr<T>(_: T) -> T {
    absurd
}

#[ghost] // avoid triggering error since this is prusti specific
#[open]
#[creusot::no_translate]
#[rustc_diagnostic_item = "prusti_expiry"]
pub fn at_expiry<'a: 'a, T>(_: T) -> T {
    absurd
}

#[trusted]
#[rustc_diagnostic_item = "prusti_plain"]
pub trait Plain: Copy {}

macro_rules! impl_plain {
    () => {};
    ( $first:ident $( $rest:ident )* ) => {
        #[trusted]
        impl Plain for $first {}
        impl_plain!{$($rest)*}
    };
}

impl_plain! {u8 u16 u32 u64 u128 i8 i16 i32 i64 i128 f32 f64 char bool}

#[trusted]
impl<T> Plain for *mut T {}

#[trusted]
impl<T> Plain for *const T {}

macro_rules! tuple_impl_plain {
    ( $($( $name:ident )+ )?) => {
        #[trusted]
        impl$(<$($name: Plain),+>)? Plain for ($($($name,)+)?) {}
    };
}

macro_rules! tuple_impl_all_plain {
    ( $first:ident $( $name:ident )* ) => {
        tuple_impl_plain!{$first $($name)*}
        tuple_impl_all_plain!{$($name)*}
    };
    () => {
         tuple_impl_plain!{}
    }
}

tuple_impl_all_plain! {A B C D E F G H I J K L}

pub trait ReplaceLifetimesWithStatic {
    #[rustc_diagnostic_item = "prusti_replace_static_user"]
    type WithStatic;
}

pub mod __prusti {

    #[rustc_diagnostic_item = "prusti_zombie_internal"]
    pub struct Zombie<T>(core::marker::PhantomData<T>);

    impl<T> Copy for Zombie<T> {}

    impl<T> Clone for Zombie<T> {
        fn clone(&self) -> Self {
            *self
        }
    }
}

#[ghost] // avoid triggering error since this is prusti specific
#[open]
#[creusot::no_translate]
#[rustc_diagnostic_item = "prusti_dbg_ty"]
pub fn __dbg_ty<T>(_: T) -> T {
    absurd
}
