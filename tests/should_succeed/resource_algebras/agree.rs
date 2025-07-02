extern crate creusot_contracts;
use creusot_contracts::{logic::ra::agree::Ag, resource::Resource, *};

#[requires(x.id() == y.id())]
#[ensures(x@ == y@)]
pub fn agreement(x: &Resource<Ag<i32>>, y: &Resource<Ag<i32>>) {
    // this result is valid iff x@ == y@
    // and it is valid by invariant
    let _ = x.join_shared(y);
}
