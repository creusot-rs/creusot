extern crate creusot_std;

mod a {
    #[allow(dead_code)]
    pub struct Y(pub super::b::X);
}

mod b {
    #[allow(dead_code)]
    pub enum X {
        A,
        B,
        C,
    }
}

pub fn f() {
    let _ = b::X::A;
    let _ = a::Y(b::X::B);
}
