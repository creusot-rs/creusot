extern crate creusot_std;
#[allow(unused)]
use creusot_std::prelude::*;

pub trait P {
    type A;
}

pub struct B(<B as P>::A);

impl P for B {
    type A = Option<Box<B>>;
}

pub fn q(x: B) {
    let _ = x.0;
}
