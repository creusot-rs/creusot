// TIME 5
extern crate creusot_std;
use creusot_std::prelude::*;

pub fn ghost_vec() {
    let mut v = Seq::new();
    proof_assert!(forall<i> v.get(i) == None);
    ghost! {
        assert!(v.is_empty());
        v.push_back(21);
        assert!(!v.is_empty());
        proof_assert!(v[0] == 21i32);
        proof_assert!(v.len() == 1);

        v.push_back(10);
        v.push_back(30);
        let len = v.len();
        proof_assert!(len == 3);
        proof_assert!(v[0] == 21i32 && v[1] == 10i32 && v[2] == 30i32);

        let get1 = v.get(1int);
        let get2 = v.get(3int);
        proof_assert!(get1 == Some(&10i32));
        proof_assert!(get2 == None);

        if let Some(x) = v.get_mut(0int) {
            *x = 42;
        }
        proof_assert!(v[0] == 42i32);

        let pop1 = v.pop_back();
        let pop2 = v.pop_back();
        let pop3 = v.pop_back();
        let pop4 = v.pop_back();
        let pop5 = v.pop_back();
        proof_assert!(pop1 == Some(30i32));
        proof_assert!(pop2 == Some(10i32));
        proof_assert!(pop3 == Some(42i32));
        proof_assert!(pop4 == None);
        proof_assert!(pop5 == None);
    };

    let mut v = Seq::new();
    ghost! {
        v.push_front(1);
        v.push_front(2);
        v.push_front(3);
        let pop1 = v.pop_front();
        let pop2 = v.pop_front();
        let pop3 = v.pop_front();
        let pop4 = v.pop_front();
        proof_assert!(pop1 == Some(3i32));
        proof_assert!(pop2 == Some(2i32));
        proof_assert!(pop3 == Some(1i32));
        proof_assert!(pop4 == None);
    };
}
