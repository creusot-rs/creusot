extern crate creusot_contracts;

use creusot_contracts::ensures;

const FOO: usize = 42;

#[ensures(result == 42usize)]
pub const fn foo() -> usize {
    FOO
}

#[ensures(result == 9usize)]
pub const fn array() -> usize {
    const X: [i32; 9] = [1; 9];
    X.len()
}

#[ensures(result == N)]
pub const fn array_param<const N: usize>() -> usize {
    let x: [u32; N] = const { [1; N] };
    x.len()
}

#[ensures(result@ == N@ + 1)]
pub const fn add_one<const N: usize>() -> usize {
    const { N + 1 }
}
