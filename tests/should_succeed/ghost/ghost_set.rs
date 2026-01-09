extern crate creusot_std;
use creusot_std::{logic::FSet, prelude::*};

pub fn ghost_map() {
    let mut set = FSet::<i32>::new();
    ghost! {
        proof_assert!(forall<k: i32> !set.contains(k));
        set.insert_ghost(1);
        let length1 = set.len_ghost();
        proof_assert!(set.contains(1i32) && !set.contains(2i32));
        proof_assert!(length1 == 1);
        let (x1, x2, x3) = (1, 2, 3); // HACK: work around an issue with promoted

        let inserted_true = set.insert_ghost(2);
        let inserted_false = set.insert_ghost(2);
        let length2 = set.len_ghost();
        proof_assert!(inserted_true && !inserted_false);
        proof_assert!(length2 == 2);
        proof_assert!(set.contains(1i32) && set.contains(2i32));

        let remove_false1 = set.remove_ghost(&x3);
        let remove_true = set.remove_ghost(&x2);
        let remove_false2 = set.remove_ghost(&x2);
        proof_assert!(!remove_false1 && remove_true && !remove_false2);
        proof_assert!(!set.contains(2i32));
        proof_assert!(set.len() == 1);

        let contains1 = set.contains_ghost(&x1);
        let contains2 = set.contains_ghost(&x2);
        let contains3 = set.contains_ghost(&x3);
        proof_assert!(contains1);
        proof_assert!(!contains2);
        proof_assert!(!contains3);
    };
}
