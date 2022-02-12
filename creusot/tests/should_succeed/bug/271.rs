fn ex() {
    let a = 0;
    match a {
        _ => {}
        0 => {}
    }
}
fn ex2() {
    let a = 0;
    match a {
        0 | 1 => {}
        1 => {}
        _ => {}
    }
}
fn ex3() {
    let a = 0;
    match a {
        0 | 1 => {}
        1 | 2 => {}
        _ => {}
    }
}
