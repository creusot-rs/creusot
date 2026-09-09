#![allow(unused)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
fn zero() -> usize {
    0usize
}

#[logic]
fn one() -> usize {
    1usize
}

#[logic]
fn two() -> usize {
    2usize
}

trait Number {
    fn number() -> usize;
}


struct Zero;
struct One;
struct Two;



impl Number for Zero {
    #[logic_alias(zero)]
    fn number() -> usize {
        0
    }
}

impl Number for One {
    #[logic_alias(one)]
    fn number() -> usize {
        1
    }
}

impl Number for Two {
    #[logic_alias(two)]
    fn number() -> usize {
        2
    }
}



#[ensures(result == forall<i> 0 <= i && i < elems@.len() ==> elems@[i] == Zero::number())]
fn all_zero(elems: &[usize]) -> bool {
    #[invariant(forall<j> 0 <= j && j < produced.len() ==> *produced[j] == Zero::number())]
    for i in elems {
        if *i != Zero::number() {
            return false;
        }
    }

    true
}

#[ensures(result == forall<i> 0 <= i && i < elems@.len() ==> elems@[i] == One::number())]
fn all_one(elems: &[usize]) -> bool {
    #[invariant(forall<j> 0 <= j && j < produced.len() ==> *produced[j] == One::number())]
    for i in elems {
        if *i != One::number() {
            return false;
        }
    }

    true
}

#[ensures(result == forall<i> 0 <= i && i < elems@.len() ==> elems@[i] == Two::number())]
fn all_two(elems: &[usize]) -> bool {
    #[invariant(forall<j> 0 <= j && j < produced.len() ==> *produced[j] == Two::number())]
    for i in elems {
        if *i != Two::number() {
            return false;
        }
    }

    true
}
