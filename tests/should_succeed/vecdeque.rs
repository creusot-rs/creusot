extern crate creusot_std;
use creusot_std::prelude::*;

use std::collections::VecDeque;

pub fn test_deque() {
    let deque: VecDeque<u32> = VecDeque::with_capacity(5);

    assert!(deque.is_empty());
    assert!(deque.len() == 0);

    let mut deque: VecDeque<u32> = VecDeque::new();

    assert!(deque.is_empty());
    assert!(deque.len() == 0);

    assert!(deque.pop_front() == None);
    assert!(deque.pop_back() == None);

    deque.push_front(1);
    deque.push_front(2);
    deque.push_back(3);

    assert!(deque.pop_front() == Some(2));
    assert!(deque.pop_back() == Some(3));
    deque.clear();
    assert!(deque.is_empty());
}

#[requires(deque@.len() == 2)]
pub fn index_mut_keeps_the_rest(deque: &mut VecDeque<u32>) {
    let first = snapshot!(deque@[0]);
    deque[1] = 7;
    proof_assert!(deque@.len() == 2);
    proof_assert!(deque@[0] == *first);
    proof_assert!(deque@[1] == 7u32);
}
