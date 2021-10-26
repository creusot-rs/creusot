// WHY3PROVE Z3
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[logic]
#[variant(seq.len())]
fn sum(seq: Seq<Int>) -> Int {
    pearlite! {
        if seq.len() === 0 { 0 }
        else {
            seq[seq.len() - 1] + sum(seq.subsequence(0, seq.len() - 1))
        }
    }
}
