extern crate creusot_contracts;

use creusot_contracts::*;

pub enum List {
    Cons(u32, Box<List>),
    Nil,
}
use List::*;

#[logic]
fn len(l: List) -> Int {
    match l {
        Cons(_, ls) => 1 + len(*ls),
        Nil => 0,
    }
}

#[logic]
fn get(l: List, ix: Int) -> Option<u32> {
    match l {
        Cons(x, ls) => match pearlite! { ix == 0 } {
            true => Some(x),
            false => get(*ls, ix - 1),
        },
        Nil => None,
    }
}

#[ensures(forall<i:Int> 0 <= i && i < len(*l) ==> get(^l, i) == Some(0u32))]
#[ensures(len(*l) == len(^l))]
pub fn all_zero(l: &mut List) {
    use List::*;
    let mut loop_l = l;

    #[invariant(zeroed,
        (forall<i:Int> 0 <= i && i < len(*loop_l) ==> get(^loop_l, i) == Some(0u32)) ==>
            forall<i:Int> 0 <= i && i < len(*l) ==> get(^l, i) == Some(0u32))]
    #[invariant(in_len, len(^loop_l) == len(*loop_l) ==> len(^l) == len(*l))]
    while let Cons(value, next) = loop_l {
        *value = 0;
        loop_l = next;
    }
}
