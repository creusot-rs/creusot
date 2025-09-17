extern crate creusot_contracts;
use creusot_contracts::*;

pub trait AssocTrait {
    #[logic]
    fn invariant(self) -> bool;
}

pub trait Trait {
    type Assoc: AssocTrait;

    #[logic]
    #[ensures(result ==> assoc.invariant())]
    fn invariant(self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
pub struct Struct;

impl AssocTrait for AssocStruct {
    #[logic(open)]
    fn invariant(self) -> bool {
        true
    }
}

impl Trait for Struct {
    type Assoc = AssocStruct;

    #[logic(open)]
    #[ensures(result ==> assoc.invariant())]
    fn invariant(self, assoc: AssocStruct) -> bool {
        true
    }
}
