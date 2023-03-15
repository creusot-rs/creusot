extern crate creusot_contracts;
use creusot_contracts::*;

// une spécification qui conduit à prouver n'importe quoi
#[requires(cond.precondition(()) && forall <b:bool> branch.precondition((b,))
           && (exists <b:bool> forall <b0:bool> cond.postcondition((),b0) ==> b0==b) )] // exprime que cond est déterministe ! Mais c'est elle qui conduit à l'absurde.
#[ensures(false)]
pub fn incorrect<C: Fn() -> bool, B: FnOnce(bool) -> ()>(cond: C, branch: B) {}

#[ensures(false)]
pub fn valid_normal(n: u32) -> u32 {
    let mut r = 0u32;
    let cond = #[ensures(result == (n > 7u32))]
    || n > 7u32;
    let branch = #[ensures((b && r == 2u32) || (!b && r==1u32))]
    |b: bool| r = if b { 2 } else { 1 };
    incorrect(cond, branch);
    r
}
