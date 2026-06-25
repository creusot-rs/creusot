extern crate creusot_std;
use creusot_std::prelude::*;

#[prophetic_alias(^b)]
fn proph(b: &mut usize) -> usize {
    *b
}

fn foo() {
    let b = &mut 0;
    let _ = snapshot! { proph(b) };
}
