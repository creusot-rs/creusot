extern crate creusot_contracts;

pub fn f() {
    let mut a = 10;
    let mut b = 10;

    let x = &mut a;
    let y = &mut b;
    let w;
    if true {
        *x = 5;
        w = x;
    } else {
        *y = 6;
        w = y;
        // *x = 5;
        // z = y;
    }

    let _ = *w;
    // assume { *z = ^z };
    // assume { ? = ? };
    // assume { ? = ? };

    // assert(a == 5 || b == 5 || c == 5);
}
