extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub struct Test {
    x: u32,
}

#[open]
#[logic((r'x) -> r'x)]
pub fn test(arg: &Test) -> &u32 {
    let Test { x } = arg;
    x
}

#[open]
#[logic((r'x) -> r'x)]
pub fn test2(arg: &Test) -> &u32 {
    test(arg)
}

#[ensures(result == test2(arg))]
pub fn test3(arg: &Test) -> &u32 {
    &arg.x
}

#[open]
#[logic((r'x) -> 'x)]
pub fn test4(arg: &Test) -> u32 {
    arg.x
}

#[open]
#[logic(('x) -> 'curr)]
pub fn test5(arg: &Test) -> u32 {
    arg.x
}

pub trait FakeRef {
    #[open]
    #[logic((r'x) -> r'x)]
    fn make_ref(&self) -> &Self {
        self
    }
}

impl<X> FakeRef for X {}

#[open]
#[logic(('x) -> 'x)]
pub fn test6(arg: Test) -> u32 {
    test4(arg.make_ref())
}

#[open]
#[logic(('x) -> r'curr)]
pub fn test7(arg: &Test) -> &u32 {
    arg.x.make_ref()
}

#[open]
#[logic((r'x) -> r'x)]
pub fn test8(arg: &Test) -> &u32 {
    arg.x.make_ref()
}

// #[logic(('x) -> r'curr)]
// pub fn test9(arg: &u32) -> &u32 {
//     arg
// }
