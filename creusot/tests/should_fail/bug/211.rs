pub enum E {
    A,
    B,
    C,
}

struct S(E);

fn ex(s: S) {
    match s.0 {
        E::A => {}
    }
}
