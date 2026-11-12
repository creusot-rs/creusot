// WHY3PROVE
#[allow(unused)]
use creusot_std::prelude::*;
use std::collections::VecDeque;

pub fn vec_insert_past_end() {
    let mut v: Vec<u8> = Vec::new();
    v.insert(1, 42);
}

pub fn vecdeque_index_past_end() -> u8 {
    let v: VecDeque<u8> = VecDeque::new();
    v[0]
}
