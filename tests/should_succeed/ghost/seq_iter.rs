extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(*result == (*s).reverse())]
pub fn reverse_ghost<T>(s: Ghost<Seq<T>>) -> Ghost<Seq<T>> {
    ghost! {
        let len = snapshot!(s.len());
        let mut result = Seq::new().into_inner();
        #[variant(*len - produced.len())]
        #[invariant(result == produced.reverse())]
        for x in s.into_inner() {
            result.push_front_ghost(x);
        }
        result
    }
}

#[ensures(result.to_owned_seq() == (*s).reverse())]
pub fn reverse_ghost_ref<T>(s: Ghost<&Seq<T>>) -> Ghost<Seq<&T>> {
    ghost! {
        let len = snapshot!(s.len());
        let mut result = Seq::new().into_inner();
        #[variant(*len - produced.len())]
        #[invariant(result == produced.reverse())]
        for x in s.into_inner() {
            result.push_front_ghost(x);
        }
        result
    }
}
