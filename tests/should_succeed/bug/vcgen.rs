extern crate creusot_contracts;
use creusot_contracts::{logic::FSet, *};

#[logic]
#[open(self)]
#[requires(!s.is_empty())]
#[variant(s.len())]
#[ensures(s.contains(result))]
#[ensures(forall<o : _> s.contains(o) ==> o <= result )]
pub fn set_max(s: FSet<Int>) -> Int {
    let x = s.peek();
    let s = s.remove(x);

    if s.is_empty() {
        x
    } else {
        let rec = set_max(s);
        if x >= rec { x } else { rec }
    }
}
