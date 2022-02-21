extern crate creusot_contracts;

use creusot_contracts::*;

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

fn multiply(x: usize, y: usize) -> usize {
    x * y
}

#[logic]
fn multiply_int(x: Int, y: Int) -> Int {
    x * y
}

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

fn sub(x: usize, y: usize) -> usize {
    x - y
}

#[logic]
fn sub_int(x: Int, y: Int) -> Int {
    x - y
}

// Precedence

fn expression(x: usize, y: usize, z: usize) -> bool {
    x / y * z == (x / y) * z
}

#[logic]
fn expression_logic(x: usize, y: usize, z: usize) -> bool {
    x / y * z == (x / y) * z
}

struct X {
    a: usize,
}

#[ensures((x.a) <= (x.a))]
fn primitive_comparison(x: X) {}

#[ensures(result === (a === b))]
fn bool_eq(a: bool, b: bool) -> bool {
    a == b
}

#[ensures(old(x) === x)]
fn old_test(x: bool) {}
