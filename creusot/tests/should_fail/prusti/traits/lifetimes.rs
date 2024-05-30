extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub trait MyTrait<X> {
    #[logic]
    fn test<'a: 'b, 'b>(x: &'a mut X) -> &'b mut X;
}

pub struct MyStruct;

impl<Y> MyTrait<Y> for MyStruct {
    #[open]
    #[logic]
    fn test<'c: 'd, 'd>(x: &'c mut Y) -> &'c mut Y {
        x
    }
}
