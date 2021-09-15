struct MyInt(usize);

fn main() {
    let mut a = (MyInt(1), MyInt(2));
    let x = &mut a;

    let z = &mut x.1;

    (*x).0 = MyInt(3);

    (a.0).0 == 3;
}
