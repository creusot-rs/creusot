extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn is_odd_logic(a: i64) -> bool {
    a & 1i64 != 0i64
}

#[logic_alias(is_odd_logic)]
pub fn is_odd(x: i64) -> bool {
    x & 1 != 0
}

#[ensures(result == forall<i> 0 <= i && i < values@.len() ==> is_odd(values@[i]))]
pub fn is_all_odd(values: &[i64]) -> bool {
    #[invariant(forall<v> 0 <= v && v < produced.len() ==> is_odd(*produced[v]))]
    for i in values {
        if !is_odd(*i) {
            return false;
        }
    }

    true
}
