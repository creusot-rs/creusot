extern crate creusot_contracts;
use creusot_contracts::*;

#[predicate(prophetic)]
#[ensures(seq.resolve() ==> result)]
fn resolve_seq<T>(seq: Seq<&mut T>) -> bool {
    pearlite! {
        forall<i: Int> #![trigger seq[i]] 0 < i && i <= seq.len() ==>
            *seq[i] == ^seq[i]
    }
}

#[predicate(prophetic)]
#[ensures(seq.resolve() ==> result)]
#[open(self)]
pub fn resolve_seq2<T>(seq: Seq<&mut T>) -> bool {
    resolve_seq(seq)
}
