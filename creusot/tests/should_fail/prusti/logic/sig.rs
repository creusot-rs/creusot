extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[logic(('x) -> ('x))]
fn test<'a>(x: &'a mut u32) -> &'a mut u32 {
    x
}
