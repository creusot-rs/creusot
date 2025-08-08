extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Tr: Sized {
    #[logic]
    fn foo(self);

    #[logic]
    #[open]
    fn bar(self) {}
}

impl<T, U> Tr for (T, U)
where
    T: Tr,
    U: Tr,
{
    #[logic]
    #[open(self)]
    fn foo(self) {
        self.bar()
    }
}
