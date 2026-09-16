extern crate creusot_std;
use creusot_std::{logic::FMap, prelude::*};

pub fn foo() {
    let mut map = snapshot!(FMap::empty());
    map = snapshot!(map.add(1, 3));
    proof_assert!(map[1] == 3);
    map = snapshot!(map.add(2, 42));
    proof_assert!(map[1] == 3 && map[2] == 42);
    map = snapshot!(map.add(1, 4));
    proof_assert!(map[1] == 4 && map[2] == 42);
}
