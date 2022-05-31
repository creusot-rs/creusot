extern crate creusot_contracts;

struct MyInt(usize);

pub fn f() {
    let mut a = (MyInt(1), MyInt(2));
    let x = &mut a;

    let _z = &mut x.1;

    (*x).0 = MyInt(3);

    let _ = (a.0).0 == 3;
}
