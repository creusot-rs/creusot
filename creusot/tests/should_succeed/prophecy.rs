fn main() {
    let mut x = 0;
    let y = &mut x;

    // assert ^y = 5

    *y = 5;
}
