// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(cond.precondition(()) && forall <b:bool> branch.precondition((b,)))]
#[ensures(exists <b:bool> cond.postcondition((),b) && branch.postcondition_once((!b,),()))]
pub fn inversed_if<C: Fn() -> bool, B: FnOnce(bool) -> ()>(cond: C, branch: B) {
    if !cond() { branch(true) } else { branch(false) }
}

#[ensures((n > 7u32 && result == 2u32) || (n <= 7u32 && result == 1u32))] // <- should fail !
pub fn valid(n: u32) -> u32 {
    let mut r = 0u32;
    let cond = #[ensures(result == (n > 7u32))]
    || n > 7u32;
    let branch = #[ensures((b && r == 2u32) || (!b && r==1u32))]
    |b: bool| r = if b { 2 } else { 1 };
    inversed_if(cond, branch);
    proof_assert! { false };
    r
}
