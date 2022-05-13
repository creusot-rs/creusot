fn promoted_none() {
    let ix = Some(0);

    match (&Some(42), &Some(43)) {
        (None, None) => panic!(),
        _ => (),
    }
}

fn promoted_int() {
    let ix = &(1 + 5 + 10);

    if *ix != 16 {
        panic!();
    }
}

fn string(s: String) {}

fn str() {
    let s = "1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890";
}
