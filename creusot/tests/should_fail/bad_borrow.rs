fn bad_borrow() {
    let mut x = 0;
    let a = &mut x;
    let b = &mut x;

    *a += *b;
}
