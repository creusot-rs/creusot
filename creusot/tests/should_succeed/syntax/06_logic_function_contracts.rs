extern crate creusot_contracts;
use creusot_contracts::{
    logic::{Int, Seq},
    *,
};

#[open]
#[logic]
#[variant(seq.len())]
pub fn sum(seq: Seq<Int>) -> Int {
    pearlite! {
        if seq.len() == 0 { 0 }
        else {
            seq[seq.len() - 1] + sum(seq.subsequence(0, seq.len() - 1))
        }
    }
}

#[open]
#[predicate]
#[variant(seq.len())]
pub fn all_zero(seq: Seq<Int>) -> bool {
    pearlite! {
        if seq.len() == 0 { true }
        else {
            seq[seq.len() - 1] == 0 && all_zero(seq.subsequence(0, seq.len() - 1))
        }
    }
}

#[open]
#[predicate]
#[variant(i)]
pub fn stupid<T>(x: T, i: Int) -> bool {
    pearlite! {
        if i <= 0 {
            true
        } else if x == x {
            stupid(x, 0)
        } else {
            false
        }
    }
}
