extern crate creusot_std;

pub struct S;

impl FromIterator<()> for S {
    fn from_iter<I: IntoIterator<Item = ()>>(_: I) -> Self {
        S
    }
}

pub fn f() {
    let _ = S::from_iter([()].into_iter());
}
