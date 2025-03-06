extern crate creusot_contracts;

pub fn f() {
    let mut a = 10;
    let b = &mut a;
    let _c: &u32 = b;
}
