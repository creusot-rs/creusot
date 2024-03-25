extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures((b, 0).0 != result ==> false)]
fn test(b: Box<u32>) -> Box<u32> {
    b
}
