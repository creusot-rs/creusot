#![feature(sized_type_properties)]
extern crate creusot_contracts;

use creusot_contracts::{Clone, *};

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

#[logic]
pub fn add_one_logic<const P: usize>() -> Int {
    pearlite! { P@ + 1 }
}

// Check instantiation of const generics
#[requires(M < usize::MAX)]
#[ensures(result@ == add_one_logic::<M>() )]
pub const fn add_one_2<const M: usize>() -> usize {
    add_one::<M>()
}

pub trait Nat {
    const VALUE: usize;
}

// associated const
#[ensures(result == N::VALUE)]
pub const fn nat<N: Nat>() -> usize {
    const { N::VALUE }
}

// Handle const params from parents
pub trait Parent<const N: usize> {
    #[requires(N@ + M@ <= usize::MAX@)]
    fn child<const M: usize>() -> usize {
        N + M
    }
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

impl<T: Nat> Nat for I2<T> {
    const VALUE: usize = T::VALUE;
}

#[ensures(result == T::VALUE)]
pub const fn nat_i2<T: Nat>() -> usize {
    const { <I2<T> as Nat>::VALUE }
}

const TUP: (usize, i32) = (42, 24);

#[requires(TUP.0 == 42usize)]
#[ensures(TUP.1 == 24i32)]
pub const fn tuple() -> (usize, i32) {
    TUP
}

pub const fn inline_tuple() {
    const ITUP: (usize, i32) = (42, 24);
    proof_assert!(ITUP == TUP);
}

struct I3<T: Nat>(T);

impl<T: Nat> Nat for I3<T> {
    const VALUE: usize = const { T::VALUE + T::VALUE };
}

pub const fn nat_i3<T: Nat>() {
    proof_assert! { <I3<T> as Nat>::VALUE@ == T::VALUE@ + T::VALUE@ };
}

// Check that const setters are called by logic VCs
#[logic]
#[ensures(<I3<T> as Nat>::VALUE@ == T::VALUE@ + T::VALUE@)]
pub fn nat_i3_logic<T: Nat>() {}

#[derive(Clone, Copy)]
pub enum Peano {
    Z,
    S(&'static Peano),
}

const PEANOS: [Peano; 2] = [Peano::Z, Peano::S(&Peano::Z)];

#[ensures(result == Peano::Z)]
pub fn zero() -> Peano {
    PEANOS[0]
}

pub const STR: &'static str = "Hello";

#[ensures(result == STR)]
pub fn str() -> &'static str {
    STR
}

// associated const from std
#[ensures(result == <T as ::std::mem::SizedTypeProperties>::IS_ZST)]
pub const fn is_zst<T>() -> bool {
    const { <T as ::std::mem::SizedTypeProperties>::IS_ZST }
}

struct Z;

// specialize associated const
#[ensures(result)]
pub const fn is_zst_z() -> bool {
    const { is_zst::<Z>() }
}

pub const MAX_ENTRIES_CAPACITY: usize = (isize::MAX as usize) / ::std::mem::size_of::<usize>();

pub fn max_entries_capacity() {
    proof_assert!(MAX_ENTRIES_CAPACITY@ > 0)
}

#[ensures(result@ == 2)]
fn some_fn_pointer() -> i32 {
    2
}

pub fn fn_pointer_test() {
    let x = &some_fn_pointer;
    let y = x();
    proof_assert!(y@ == 2);
}
