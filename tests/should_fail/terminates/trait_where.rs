// Trait definition is recursive through a where clause of a method
extern crate creusot_std;
use creusot_std::prelude::*;

// Recursive trait definition
pub trait Tr<T>: Sized {
    #[logic]
    #[ensures(false)]
    fn f(&self, x: &T)
    where
        Self: Tr<Self>;
}

impl<U> Tr<i32> for U {
    #[logic]
    #[ensures(false)]
    fn f(&self, x: &i32)
    where
        U: Tr<U>,
    {
        self.f(self)
    }
}

#[logic]
#[ensures(false)]
pub fn g() {
    1i32.f(&1i32)
}
