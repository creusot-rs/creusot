use base_macros::*;

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
#[rustc_diagnostic_item = "prusti_at"]
pub fn at<'a: 'a, T>(_: T) -> T {
    absurd
}

#[trusted]
#[rustc_diagnostic_item = "prusti_plain"]
pub trait Plain: Copy {}

#[rustc_diagnostic_item = "prusti_snap_eq"]
/// Trait representing types that can be checked for equality when using Prusti contracts
pub trait SnapEq {}

impl<X> SnapEq for X {}

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

#[rustc_diagnostic_item = "prusti_zombie_internal"]
pub struct Zombie<T>(core::marker::PhantomData<T>);

impl<T> Copy for Zombie<T> {}

impl<T> Clone for Zombie<T> {
    fn clone(&self) -> Self {
        *self
    }
}

#[ghost] // avoid triggering error since this is prusti specific
#[open]
#[creusot::no_translate]
#[rustc_diagnostic_item = "prusti_dbg_ty"]
pub fn __dbg_ty<T>(_: T) -> T {
    absurd
}
