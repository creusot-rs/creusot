struct MyInt(usize);

fn main() {
    let mut a = (MyInt(10), MyInt(5));
    let b = &mut a;

    let c = &mut b.1;
    let d = &mut b.0;

    (*c).0 != (*d).0;
}
