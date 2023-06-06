extern crate creusot_contracts;
use creusot_contracts::*;

pub trait AssocTrait {
    #[predicate]
    fn invariant(self) -> bool;
}

pub trait Trait {
    type Assoc: AssocTrait;

    #[predicate]
    #[ensures(result ==> assoc.invariant())]
    fn invariant(self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
pub struct Struct;

impl AssocTrait for AssocStruct {
    #[open]
    #[predicate]
    fn invariant(self) -> bool {
        true
    }
}

impl Trait for Struct {
    type Assoc = AssocStruct;

    #[open]
    #[predicate]
    #[ensures(result ==> assoc.invariant())]
    fn invariant(self, assoc: AssocStruct) -> bool {
        true
    }
}
