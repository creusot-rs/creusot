extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
fn requires_with_static<X>(x: WithStatic<X>) {}

#[logic]
fn call_without_static<'a>(x: &'a u32) {
    requires_with_static::<&u32>(x)
}