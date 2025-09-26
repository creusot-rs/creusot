// Ensures that variants are correctly checked when recursing while substituing some types.

extern crate creusot_contracts;
use creusot_contracts::{logic::WellFounded, *};

pub trait MyTrait {
    #[logic]
    fn as_int(self) -> u32;

    #[requires(self.as_int()@ - x@ >= 0)]
    #[ensures(result@ == self.as_int()@ - x@)]
    #[check(terminates)]
    fn sub(self, x: u32) -> u32;
}
impl MyTrait for u32 {
    #[logic(open)]
    fn as_int(self) -> u32 {
        self
    }

    #[check(terminates)]
    #[requires(self@ - x@ >= 0)]
    #[ensures(result@ == self@ - x@)]
    fn sub(self, x: u32) -> u32 {
        self - x
    }
}

#[allow(unconditional_recursion)]
#[variant(arg_0)]
#[check(terminates)]
#[ensures(result == 0u32)]
pub fn foo<T: WellFounded + MyTrait>(arg_0: T) -> u32 {
    foo(0)
}
