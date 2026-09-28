use creusot_std::prelude::*;

#[logic]
pub fn logic1(x: u32) -> bool {
    let _ = x;
    true
}

#[logic]
pub fn logic_transmute<T, U>(x: &T) -> U {
    let _ = x;
    creusot_std::logic::any()
}

#[logic_alias(logic1)]
pub fn hybrid(x: u32) -> bool {
    let _ = x;
    false
}

use core::mem::transmute_copy;
extern_spec!(
    #[logic_alias(logic_transmute::<T, U>)]
    unsafe fn transmute_copy<T, U>(x: &T) -> U;
);

#[creusot::decl::logic]
#[creusot_std::macros::requires(true)]
#[creusot_std::macros::ensures(!result)]
pub fn uses_logic_alias(x: f64) -> bool {
    let x = unsafe { transmute_copy(&x) };
    hybrid(x)
}
