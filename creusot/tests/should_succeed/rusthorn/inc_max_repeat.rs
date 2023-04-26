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

#[requires(a <= 1_000_000u32 && b <= 1_000_000u32 && n <= 1_000_000u32)]
pub fn inc_max_repeat(mut a: u32, mut b: u32, n: u32) {
    #[invariant(val_bound, a@ <= 1_000_000 + produced.len() && b@ <= 1_000_000 + produced.len())]
    #[invariant(diff_bound, a@ >= b@ + produced.len() || b@ >= a@ + produced.len()) ]
    for _ in 0..n {
        let mc = take_max(&mut a, &mut b);
        *mc += 1;
    }
    assert!(a >= b + n || b >= a + n);
}
