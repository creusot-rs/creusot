extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
#[ensures(^mma == *mmb && ^mmb == *mma)]
fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32) {
    std::mem::swap(mma, mmb);
}

#[requires(*ma <= 1_000_000u32 && *mb <= 1_000_000u32 && *mc <= 1_000_000u32)]
#[ensures(^ma != ^mb && ^mb != ^mc && ^mc != ^ma)]
fn inc_max_3<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32, mut mc: &'a mut u32) {
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    if *mb < *mc {
        swap(&mut mb, &mut mc);
    }
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    *ma += 2;
    *mb += 1;
}

#[requires(a <= 1_000_000u32 && b <= 1_000_000u32 && c <= 1_000_000u32)]
pub fn test_inc_max_3(mut a: u32, mut b: u32, mut c: u32) {
    inc_max_3(&mut a, &mut b, &mut c);
    assert!(a != b && b != c && c != a);
}
