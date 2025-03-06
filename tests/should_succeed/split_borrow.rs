extern crate creusot_contracts;

struct MyInt(usize);

fn z() -> bool {
    true
}

pub fn f() {
    let mut x = (MyInt(1), MyInt(2));
    let y = &mut x;

    if z() {
        (*y).1 = MyInt(4);
    } else {
        (*y).0 = MyInt(10);
    }

    // Keep the borrow alive until after the if statement
    (y.0).0;
}

pub fn g() {
    let mut a = (MyInt(1), MyInt(2));
    let x = &mut a;

    let _z = &mut x.1;

    (*x).0 = MyInt(3);

    let _ = (a.0).0 == 3;
}
