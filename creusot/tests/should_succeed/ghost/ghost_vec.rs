extern crate creusot_contracts;
use creusot_contracts::{ghost::GhostVec, *};

pub fn ghost_vec() {
    let mut v = GhostVec::new();
    proof_assert!(forall<i: Int> v@.get(i) == None);
    let length1 = ghost! {
        v.push(21);
        v.len()
    };
    proof_assert!(v@[0] == 21i32);
    proof_assert!(length1.inner() == 1);

    let length2 = ghost! {
        v.push(10);
        v.push(30);
        v.len()
    };
    proof_assert!(length2.inner() == 3);
    proof_assert!(v@[0] == 21i32 && v@[1] == 10i32 && v@[2] == 30i32);

    let get1 = ghost!(v.get(*Int::new(1)));
    let get2 = ghost!(v.get(*Int::new(3)));
    proof_assert!(get1.inner() == Some(&10i32));
    proof_assert!(get2.inner() == None);

    ghost! {
        if let Some(x) = v.get_mut(*Int::new(0)) {
            *x = 42;
        }
    };
    proof_assert!(v@[0] == 42i32);

    let pop1 = ghost!(v.pop());
    let pop2 = ghost!(v.pop());
    let pop3 = ghost!(v.pop());
    let pop4 = ghost!(v.pop());
    let pop5 = ghost!(v.pop());
    proof_assert!(pop1.inner() == Some(30i32));
    proof_assert!(pop2.inner() == Some(10i32));
    proof_assert!(pop3.inner() == Some(42i32));
    proof_assert!(pop4.inner() == None);
    proof_assert!(pop5.inner() == None);
}
