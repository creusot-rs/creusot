extern crate creusot_contracts;
use creusot_contracts::*;

// une spécification qui conduit à prouver n'importe quoi
#[requires(cond.postcondition((),true) )] // exprime que cond est déterministe ! Mais c'est elle qui conduit à l'absurde.
#[ensures(false)]
pub fn incorrect<C: Fn() -> bool, B: FnOnce(bool) -> ()>(cond: C, branch: B) {}
