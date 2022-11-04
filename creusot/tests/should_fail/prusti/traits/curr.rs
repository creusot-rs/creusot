extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait MyTrait {
    #[logic(('x) -> 'x)]
    fn test<'a, X>(x: &'a mut X) -> &'a mut X;
}

struct MyStruct;

impl MyTrait for MyStruct {
    #[logic(('x) -> 'x)]
    fn test<'curr, Y>(x: &'curr mut Y) -> &'curr mut Y {
        x
    }
}
