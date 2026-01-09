extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr: Sized {
    #[logic]
    fn foo(self);

    #[logic(open)]
    fn bar(self) {}
}

impl<T, U> Tr for (T, U)
where
    T: Tr,
    U: Tr,
{
    #[logic(open(self))]
    fn foo(self) {
        self.bar()
    }
}
