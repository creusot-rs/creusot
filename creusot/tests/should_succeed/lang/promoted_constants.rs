extern crate creusot_contracts;

pub fn promoted_none() {
    let _ix = Some(0);

    match (&Some(42), &Some(43)) {
        (None, None) => panic!(),
        _ => (),
    }
}

pub fn promoted_int() {
    let ix = &(1 + 5 + 10);

    if *ix != 16 {
        panic!();
    }
}

pub fn string(_s: String) {}

pub fn str() {
    let _s = "1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890";
}
