extern crate creusot_contracts;
use creusot_contracts::*;

pub fn ghost_vec() {
    let mut v = Seq::new();
    proof_assert!(forall<i: Int> v.get(i) == None);
    ghost! {
        v.push_ghost(21);
        proof_assert!(v[0] == 21i32);
        proof_assert!(v.len() == 1);

        v.push_ghost(10);
        v.push_ghost(30);
        let len = v.len_ghost();
        proof_assert!(len == 3);
        proof_assert!(v[0] == 21i32 && v[1] == 10i32 && v[2] == 30i32);

        let get1 = v.get_ghost(*Int::new(1));
        let get2 = v.get_ghost(*Int::new(3));
        proof_assert!(get1 == Some(&10i32));
        proof_assert!(get2 == None);

        if let Some(x) = v.get_mut_ghost(*Int::new(0)) {
            *x = 42;
        }
        proof_assert!(v[0] == 42i32);

        let pop1 = v.pop_ghost();
        let pop2 = v.pop_ghost();
        let pop3 = v.pop_ghost();
        let pop4 = v.pop_ghost();
        let pop5 = v.pop_ghost();
        proof_assert!(pop1 == Some(30i32));
        proof_assert!(pop2 == Some(10i32));
        proof_assert!(pop3 == Some(42i32));
        proof_assert!(pop4 == None);
        proof_assert!(pop5 == None);
    };
}
