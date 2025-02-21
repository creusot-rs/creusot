extern crate creusot_contracts;

pub fn f() {
    let mut a = 10;
    let b = &mut a;
    *b = 5;
    loop {
        if true {
            break;
        }
    }
    let _ = a == 15;
}
