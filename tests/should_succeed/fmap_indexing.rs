extern crate creusot_contracts;
use creusot_contracts::{logic::FMap, prelude::*};

pub fn foo() {
    let mut map = snapshot!(FMap::empty());
    map = snapshot!(map.insert(1, 3));
    proof_assert!(map[1] == 3);
    map = snapshot!(map.insert(2, 42));
    proof_assert!(map[1] == 3 && map[2] == 42);
    map = snapshot!(map.insert(1, 4));
    proof_assert!(map[1] == 4 && map[2] == 42);
}
