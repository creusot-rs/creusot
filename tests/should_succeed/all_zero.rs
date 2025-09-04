extern crate creusot_contracts;

use creusot_contracts::{logic::Int, *};

pub enum List {
    Cons(u32, Box<List>),
    Nil,
}
use List::*;

impl List {
    #[logic]
    pub fn len(self) -> Int {
        match self {
            Cons(_, ls) => 1 + ls.len(),
            Nil => 0,
        }
    }

    #[logic]
    pub fn get(self, ix: Int) -> Option<u32> {
        match self {
            Cons(x, ls) => match pearlite! { ix == 0 } {
                true => Some(x),
                false => ls.get(ix - 1),
            },
            Nil => None,
        }
    }
}

#[ensures(forall<i> 0 <= i && i < l.len() ==> (^l).get(i) == Some(0u32))]
#[ensures((*l).len() == (^l).len())]
pub fn all_zero(l: &mut List) {
    use List::*;
    let old_l = snapshot! { l };
    let mut loop_l = l;

    #[invariant(
        (forall<i> 0 <= i && i < loop_l.len() ==> (^loop_l).get(i) == Some(0u32)) ==>
            forall<i> 0 <= i && i < old_l.len() ==> (^old_l).get(i) == Some(0u32))]
    #[invariant((^loop_l).len() == loop_l.len() ==> (^old_l).len() == old_l.len())]
    while let Cons(value, next) = loop_l {
        *value = 0;
        loop_l = next;
    }
}
