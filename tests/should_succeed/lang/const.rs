#![feature(sized_type_properties)]
extern crate creusot_contracts;

use creusot_contracts::*;

const FOO: usize = 42;

// Top-level const
#[ensures(result == 42usize)]
pub const fn foo() -> usize {
    FOO
}

// Const items in a function
#[ensures(result == 52usize)]
pub const fn array() -> usize {
    const X: [i32; 9] = [1; 9];
    const Y: [i32; FOO + 1] = [1; FOO + 1];
    X.len() + Y.len()
}

// const generics and const expressions
#[ensures(result == N)]
pub const fn array_param<const N: usize>() -> usize {
    let x: [u32; N] = const { [1; N] };
    x.len()
}

// overflow check in const expressions
#[requires(N < usize::MAX)]
#[ensures(result@ == N@ + 1)]
pub const fn add_one<const N: usize>() -> usize {
    const { N + 1 }
}

pub trait Nat {
    const VALUE: usize;
}

// associated const
#[ensures(result == N::VALUE)]
pub const fn nat<N: Nat>() -> usize {
    const { N::VALUE }
}

#[allow(dead_code)]
struct I<'a, T: 'a, const N: usize, U>(&'a T, U);

impl<'a, T: 'a, const N: usize, U> Nat for I<'a, T, N, U> {
    const VALUE: usize = N;
}

// impl associated const using `const` generic (test indexing into GenericArgsRef)
#[ensures(result == N)]
pub const fn nat_i<'a, T: 'a, const N: usize, U>() -> usize {
    const { nat::<I<'a, T, N, U>>() }
}

struct I2<T: Nat>(T);

impl<T:Nat> Nat for I2<T> {
    const VALUE: usize = T::VALUE;
}

#[ensures(result == T::VALUE)]
pub const fn nat_i2<T: Nat>() -> usize {
    const { <I2<T> as Nat>::VALUE }
}

/*
// associated const from std
#[ensures(result == T::IS_ZST)]
pub const fn is_zst<T: ::std::mem::SizedTypeProperties>() -> bool {
    const { T::IS_ZST }
}

struct Z;

// specialize associated const
#[ensures(result)]
pub const fn is_zst_z() -> bool {
    const { is_zst::<Z>() }
}
 */