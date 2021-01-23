// SHOULD_SUCCEED: parse-print
#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;

use creusot_contracts::*;

enum Option<T> {
    None,
    Some(T),
}

use Option::*;

pub struct List {
    val: u32,
    next: Option<Box<List>>,
}

pub fn index_mut(mut l: &mut List, mut ix: usize) -> &mut u32 {
    while ix > 0 {
        invariant!(todo, true);
        match l.next {
            Some(ref mut n) => {
                l = n;
            }
            None => panic!(),
        }
        ix -= 1;
    }

    &mut l.val
}

// Ensure that this performs a set on the list
pub fn write(l: &mut List, ix: usize, val: u32) {
    *index_mut(l, ix) = val;
}

fn main() {
    let mut l = List {
        val: 1,
        next: Some(Box::new(List {
            val: 10,
            next: None,
        })),
    };
    write(&mut l, 0, 2);
    let l2 = List {
        val: 2,
        next: Some(Box::new(List {
            val: 10,
            next: None,
        })),
    };

    // assert(l, l2);
}
