extern crate creusot_contracts;
use creusot_contracts::*;

#[predicate(prophetic)]
#[ensures(resolve(&seq) ==> result)]
fn resolve_seq<T>(seq: Vec<&mut T>) -> bool {
    pearlite! {
        forall<i> #[trigger(seq@[i])] 0 <= i && i < seq@.len() ==>
            *seq@[i] == ^seq@[i]
    }
}

#[predicate(prophetic)]
#[ensures(resolve(&seq) ==> result)]
#[open(self)]
pub fn resolve_seq2<T>(seq: Vec<&mut T>) -> bool {
    resolve_seq(seq)
}
