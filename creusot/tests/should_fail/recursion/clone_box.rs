#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

struct S;

impl Clone for S {
    fn clone(&self) -> Self {
        let _ = Box::new(S).clone();
        S
    }
}
