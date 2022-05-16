// WHY3PROVE NO_SPLIT Z3
extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(if *ma >= *mb { *mb == ^mb && result == ma }
                   else { *ma == ^ma && result == mb })]
fn take_max<'a>(ma: &'a mut u32, mb: &'a mut u32) -> &'a mut u32 {
    if *ma >= *mb {
        ma
    } else {
        mb
    }
}

#[requires(a <= 1_000_000u32 && b <= 1_000_000u32)]
fn inc_max(mut a: u32, mut b: u32) {
    let mc = take_max(&mut a, &mut b);
    *mc += 1;
    assert!(a != b);
}
