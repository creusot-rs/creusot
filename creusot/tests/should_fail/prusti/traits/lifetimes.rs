extern crate creusot_contracts;
use creusot_contracts::prusti::*;

trait MyTrait<X> {
    #[logic(('x) -> 'x)]
    fn test<'a: 'b, 'b>(x: &'a mut X) -> &'b mut X;
}

struct MyStruct;

impl<Y> MyTrait<Y> for MyStruct {
    #[logic(('x) -> 'x)]
    fn test<'c: 'd, 'd>(x: &'c mut Y) -> &'c mut Y {
        x
    }
}
