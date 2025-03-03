#![allow(unreachable_code)]

extern crate creusot_contracts;
use creusot_contracts::*;

pub fn should_not_return() {
    ghost! {
        return;
    };
}

pub fn should_not_return_value() -> i32 {
    ghost! {
        return 42;
    };
}

pub fn should_not_break() {
    for _ in 0..10 {
        ghost! {
            break;
        };
    }
}

pub fn should_not_continue() {
    for _ in 0..10 {
        ghost! {
            continue;
        };
    }
}
