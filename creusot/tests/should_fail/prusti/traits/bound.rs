extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait MyTrait {
    #[logic('u where 'curr: 'u)]
    fn test<'a, X: Copy>(x: &'a mut X) -> X;
}

struct MyStruct;

impl MyTrait for MyStruct {
    #[logic('x where 'curr: 'x)]
    fn test<'x, Y: Copy>(x: &'x mut Y) -> Y {
        at_expiry::<'x>(*x)
    }
}
