fn main() {
    let mut a = 10;
    let b = &mut a;
    *b = 5;
    loop {
        if true {
            break;
        }
    }
    a == 15;
}
