extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;


#[logic(('curr) -> 'x)]
fn use_snap<'a>(x: &'a u32) -> &'a u32 {
    snap(x)
}