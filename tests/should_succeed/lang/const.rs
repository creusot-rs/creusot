extern crate creusot_contracts;

use creusot_contracts::ensures;

const FOO: usize = 42;

#[ensures(result == 42usize)]
pub fn foo() -> usize {
    FOO
}
