extern crate creusot_contracts;

pub fn f() {
    let mut a = 10;
    let mut b = 10;
    let mut c = 10;

    let x = &mut a;
    let y = &mut b;
    let z = &mut c;
    let w;

    match 3 {
        1 => {
            *x = 6;
            w = x;
        }
        2 => {
            *y = 7;
            w = y;
        }
        _ => {
            *z = 8;
            w = z;
        }
    }

    *w = 5;

    assert!(c == 5);
}

struct MyInt(usize);

pub fn g() {
    let mut a = (MyInt(10), MyInt(5));
    let b = &mut a;

    let c = &mut b.1;
    let d = &mut b.0;

    let _ = (*c).0 != (*d).0;
}

pub fn h() {
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
