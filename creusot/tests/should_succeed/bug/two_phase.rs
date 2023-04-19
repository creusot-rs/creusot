extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(@((^v)@)[v@.len()] == v@.len())]
pub fn test(v: &mut Vec<usize>) {
    v.push(v.len());
}
