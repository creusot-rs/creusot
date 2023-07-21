use crate::*;

pub type SizedW<T> = Box<T>;

pub trait MakeSized {
    #[ghost]
    #[why3::attr = "inline:trivial"]
    fn make_sized(self) -> SizedW<Self>;
}

impl<T: ?Sized> MakeSized for T {
    #[trusted]
    #[ghost]
    #[open(self)]
    #[ensures(*result == self)]
    fn make_sized(self) -> SizedW<Self> {
        absurd
    }
}

#[allow(unconditional_recursion)]
#[ghost]
#[open(self)]
#[requires(false)]
#[ensures(false)]
#[variant(0)]
pub fn unreachable<T>() -> T {
    unreachable()
}

#[ghost]
#[open(self)]
#[requires(op != None)]
#[ensures(Some(result) == op)]
pub fn unwrap<T>(op: Option<T>) -> T {
    match op {
        Some(t) => t,
        None => unreachable(),
    }
}
