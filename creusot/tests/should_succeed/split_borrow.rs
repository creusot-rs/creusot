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
