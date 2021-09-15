mod a {
    pub struct Y(pub super::b::X);
}

mod b {
    pub enum X {
        A,
        B,
        C,
    }
}

fn main() {
    let _ = b::X::A;
    let _ = a::Y(b::X::B);
}
