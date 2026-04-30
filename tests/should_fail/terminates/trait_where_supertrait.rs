// Same as `trait_where.rs` but recursion goes through a supertrait
extern crate creusot_std;
use creusot_std::prelude::*;

trait Q<T>: Sized {
    #[logic]
    fn f(self, x: T)
    where
        Self: P<Self>;
}

trait P<T>: Q<T> {}

impl<T> Q<i32> for T {
    #[logic]
    #[ensures(false)]
    fn f(self, x: i32)
    where
        Self: P<Self>,
    {
        self.f(self)
    }
}

impl P<i32> for i32 {}

#[logic]
#[ensures(false)]
pub fn g() {
    0i32.f(0i32)
}
