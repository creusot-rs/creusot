fn main() {
    let mut x = 1;

    let y = &mut x;
    let d = y;
    let z = d;

    *z = 2;

    // assert_eq!(x, 2);

    x == 2;
}
