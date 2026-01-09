extern crate creusot_std;

pub trait Tr<const N: usize> {
    fn f();

    fn g(x: [usize; N]) -> usize;
}

pub struct S;

impl Tr<45> for S {
    fn f() {}

    fn g(x: [usize; 45]) -> usize {
        x.len()
    }
}
