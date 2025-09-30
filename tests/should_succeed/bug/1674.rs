extern crate creusot_contracts;
use creusot_contracts::*;

pub fn f(p: *const [usize]) {
    let q = p as *const usize;
    proof_assert!(p.addr_logic() == q.addr_logic());
    let r = q as *const ();
    proof_assert!(q.addr_logic() == r.addr_logic());
}
