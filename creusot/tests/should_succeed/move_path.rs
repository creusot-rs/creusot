extern crate creusot_contracts;

pub fn f() {
    let mut x = 1;

    let y = &mut x;
    let d = y;
    let z = d;

    let _ = *z = 2;

    // assert_eq!(x, 2);

    let _ = x == 2;
}
