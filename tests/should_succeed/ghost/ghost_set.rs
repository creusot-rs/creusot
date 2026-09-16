extern crate creusot_std;
use creusot_std::{logic::FSet, prelude::*};

pub fn ghost_map() {
    let mut set = FSet::<i32>::new();
    ghost! {
        proof_assert!(forall<k: i32> !set.contains(&k));
        set.insert(1);
        let length1 = set.len();
        proof_assert!(set.contains_logic(1i32) && !set.contains_logic(2i32));
        proof_assert!(length1 == 1);
        let (x1, x2, x3) = (1, 2, 3); // HACK: work around an issue with promoted

        let inserted_true = set.insert(2);
        let inserted_false = set.insert(2);
        let length2 = set.len();
        proof_assert!(inserted_true && !inserted_false);
        proof_assert!(length2 == 2);
        proof_assert!(set.contains_logic(1i32) && set.contains_logic(2i32));

        let delete_false1 = set.delete(&x3);
        let delete_true = set.delete(&x2);
        let delete_false2 = set.delete(&x2);
        proof_assert!(!delete_false1 && delete_true && !delete_false2);
        proof_assert!(!set.contains_logic(2i32));
        proof_assert!(set.len() == 1);

        let contains1 = set.contains(&x1);
        let contains2 = set.contains(&x2);
        let contains3 = set.contains(&x3);
        proof_assert!(contains1);
        proof_assert!(!contains2);
        proof_assert!(!contains3);
    };
}
