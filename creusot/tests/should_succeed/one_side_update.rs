extern crate creusot_contracts;

struct MyInt(usize);

pub fn f() {
    let mut a = MyInt(10);
    let b = &mut a;
    if true {
        let _ = a.0 == 10;
    } else {
        *b = MyInt(5);
    }
}
