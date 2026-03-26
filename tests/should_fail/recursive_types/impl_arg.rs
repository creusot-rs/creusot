extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Q {
    #[logic]
    #[ensures(false)]
    fn f(self, x: impl Q);
}

impl Q for i32 {
    #[logic]
    #[ensures(false)]
    fn f(self, x: impl Q) {
        x.f(x)
    }
}

#[logic]
#[ensures(false)]
pub fn g() {
    0i32.f(0i32)
}
