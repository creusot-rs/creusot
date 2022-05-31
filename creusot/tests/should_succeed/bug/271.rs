#![allow(unreachable_patterns)]

extern crate creusot_contracts;

pub fn ex() {
    let a = 0;
    match a {
        _ => {}
        0 => {}
    }
}

pub fn ex2() {
    let a = 0;
    match a {
        0 | 1 => {}
        1 => {}
        _ => {}
    }
}

pub fn ex3() {
    let a = 0;
    match a {
        0 | 1 => {}
        1 | 2 => {}
        _ => {}
    }
}
