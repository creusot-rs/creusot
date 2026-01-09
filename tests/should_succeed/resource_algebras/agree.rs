extern crate creusot_std;
use creusot_std::{ghost::resource::Resource, logic::ra::agree::Ag, prelude::*};

#[requires(x.id() == y.id())]
#[ensures(x@ == y@)]
pub fn agreement(x: &Resource<Ag<i32>>, y: &Resource<Ag<i32>>) {
    // this result is valid iff x@ == y@
    // and it is valid by invariant
    let _ = x.join_shared(y);
}
