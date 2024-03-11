use crate::*;

// FIXME: better doc
/// Any item that implements `Ghost` must **not** be able to break the ownership rules,
/// be it in ghost or runtime code.
///
/// Additionnaly, it should be zero-sized, so that it's not possible to extract
/// information from a ghost bloc and use it in normal code.
#[rustc_diagnostic_item = "ghost_trait"]
#[trusted]
pub trait Ghost {}

macro_rules! impl_ghost_tuple {
    ($($ty_param:ident),*) => {
        impl_ghost_tuple!{ @inner $($ty_param,)* || []; }
    };
    (@inner $ty_param:ident, $($rest:ident,)* || $( [ $($done:ident,)* ] ;)*) => {
        impl_ghost_tuple! {
            @inner $($rest,)* ||
            [] ; $( [ $ty_param, $($done,)* ] ;)*
        }
    };
    (@inner || $( [ $($done:ident,)* ] ;)*) => {
        $(
            #[trusted]
            impl<$($done : Ghost),*> Ghost for ($($done,)*) {}
        )*
    };
}

impl_ghost_tuple! { T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }

#[trusted]
impl<T> Ghost for Snapshot<T> {}
