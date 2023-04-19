#![allow(dead_code)]

extern crate creusot_contracts;

use creusot_contracts::{logic::Int, *};

#[requires(y@ > 0)]
fn division(x: usize, y: usize) -> usize {
    x / y
}

// #[logic]
// fn division_logic(x : usize, y : usize) -> usize {
//     x / y
// }

#[logic]
fn division_int(x: Int, y: Int) -> Int {
    x / y
}

#[requires(y@ > 0)]
fn modulus(x: usize, y: usize) -> usize {
    x % y
}

// #[logic]
// fn modulus_logic(x : usize, y : usize) -> usize {
//     x % y
// }

#[logic]
fn modulus_int(x: Int, y: Int) -> Int {
    x % y
}

#[requires(x@ * y@ <= @usize::MAX)]
fn multiply(x: usize, y: usize) -> usize {
    x * y
}

#[logic]
fn multiply_int(x: Int, y: Int) -> Int {
    x * y
}

#[requires(x@ + y@ <= @usize::MAX)]
fn add(x: usize, y: usize) -> usize {
    x + y
}

#[logic]
fn add_int(x: Int, y: Int) -> Int {
    x + y
}

// #[logic]
// fn add_logic(x : usize, y : usize) -> usize {
//     x + y
// }

#[requires(x@ - y@ >= 0)]
fn sub(x: usize, y: usize) -> usize {
    x - y
}

#[logic]
fn sub_int(x: Int, y: Int) -> Int {
    x - y
}

// Precedence

#[requires(y@ > 0)]
#[requires(x@ / y@ * z@ <= @usize::MAX)]
#[ensures(result)]
fn expression(x: usize, y: usize, z: usize) -> bool {
    x / y * z == (x / y) * z
}

#[logic]
#[ensures(result)]
fn expression_logic(x: usize, y: usize, z: usize) -> bool {
    x / y * z == (x / y) * z
}

struct X {
    a: usize,
}

#[ensures(x.a <= x.a)]
fn primitive_comparison(x: X) {}

#[ensures(result == (a == b))]
fn bool_eq(a: bool, b: bool) -> bool {
    a == b
}

#[ensures(old(x) == x)]
fn old_test(x: bool) {}
