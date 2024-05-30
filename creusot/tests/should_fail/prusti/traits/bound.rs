extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub trait MyTrait {
    #[logic('u where 'now: 'u)]
    fn test<'a, X: Copy>(x: &'a mut X) -> X;
}

pub struct MyStruct;

impl MyTrait for MyStruct {
    #[open]
    #[logic('x where 'now: 'x)]
    fn test<'x, Y: Copy>(x: &'x mut Y) -> Y {
        at::<'x>(*x)
    }
}
