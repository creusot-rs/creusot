extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[variant(42)]
#[ensures(*result == 42u32)]
fn give_static() -> &'static mut u32 {
    give_static()
}

#[ensures(*old(give_static()) == 42u32)]
fn test() {}
