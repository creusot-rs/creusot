extern crate creusot_contracts;

use creusot_contracts::*;

#[requires(precond2())]
#[ensures(false)]
fn test_sym_elab() {
    true;
}

// fn test_sym_elab2() {
//   test_sym_elab();
// }

#[predicate]
fn precond2() -> bool {
    true
}
