extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait MyTrait {
    #[logic]
    fn test<'a, X>(x: &'a mut X) -> &'a mut X;
}

struct MyStruct;

impl MyTrait for MyStruct {
    #[logic]
    fn test<'now, Y>(x: &'now mut Y) -> &'now mut Y {
        x
    }
}
