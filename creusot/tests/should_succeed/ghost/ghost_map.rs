extern crate creusot_contracts;
use creusot_contracts::{ghost::GhostMap, *};

pub fn ghost_map() {
    let mut ghost_map = GhostMap::<i32, i32>::new();
    ghost! {
        let map = &mut *ghost_map;
        proof_assert!(forall<k: i32> !map@.contains(k));
        map.insert(1, 21);
        let length1 = map.len();
        proof_assert!(map@.lookup(1i32) == 21i32);
        proof_assert!(length1 == 1);
        let (x1, x2, x3) = (1, 2, 3); // HACK: work around an issue with promoted
        if let Some(x) = map.get_mut(&x1) {
            *x = 42;
        }
        proof_assert!(map@.lookup(1i32) == 42i32);

        let inserted_none = map.insert(2, 50);
        let inserted_some = map.insert(2, 100);
        let length2 = map.len();
        proof_assert!(inserted_none == None);
        proof_assert!(inserted_some == Some(50i32));
        proof_assert!(length2 == 2);
        proof_assert!(map@.lookup(2i32) == 100i32);
        proof_assert!(map@.lookup(1i32) == 42i32);

        let remove_none1 = map.remove(&x3);
        let remove_some = map.remove(&x2);
        let remove_none2 = map.remove(&x2);
        proof_assert!(remove_none1 == None);
        proof_assert!(remove_some == Some(100i32));
        proof_assert!(remove_none2 == None);
        proof_assert!(map@.get(2i32) == None);

        let contains1 = map.contains(&x1);
        let contains2 = map.contains(&x2);
        let contains3 = map.contains(&x3);
        proof_assert!(contains1);
        proof_assert!(!contains2);
        proof_assert!(!contains3);

        let get1 = map.get(&x1);
        let get2 = map.get(&x2);
        let get3 = map.get(&x3);
        proof_assert!(get1 == Some(&42i32));
        proof_assert!(get2 == None);
        proof_assert!(get3 == None);
    };
}
