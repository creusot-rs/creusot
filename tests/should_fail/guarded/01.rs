extern crate creusot_std;
use creusot_std::{invariant::Guarded, logic::Mapping};

pub fn f(g: Guarded<&mut i32, Mapping<i32, bool>>) -> &mut i32 {
    let b = g.inner;
    b
}
