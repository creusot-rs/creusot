// WHY3PROVE Z3
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[ensures(@(@^v)[(@v).len()] === (@v).len())]
fn test(v: &mut Vec<usize>) {
    v.push(v.len());
}
