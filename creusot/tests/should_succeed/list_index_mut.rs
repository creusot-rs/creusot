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

// Supposer `get ix l` logique `len l` logique

// #[requires(param_ix < len param_l@now)]
// #[ensures(result@now == get param_ix@pre param_l@pre@now)]
// #[ensures(result@fin == get param_ix@pre param_l@pre@fin)]
// #[ensures(forall i <> param_ix. get i param_l@pre@fin == get i param_l@pre@now)]
// #[ensures(len param_l@pre@fin == len param_l@pre@now)]
pub fn index_mut(mut l: &mut List, mut ix: usize) -> &mut u32 {
    // let mut l = param_l;
    // let mut ix = param_ix;

    while ix > 0 {
        // invariant!(ix_remaining_now, get ix l@now == get param_ix l@pre@now);
        // invariant!(ix_remaining_fin, get ix l@fin == get param_ix l@pre@now);
        // invariant!(seen_unchanged,
        //     (forall 0 <= i < len (l@now). get i l@fin == get i l@now) ->
        //     (forall 0 <= i < len (l@pre@now). get i l@pre@fin == get i l@pre@now)
        // );
        // invariant!(length, len param_l@fin = len param_l@now);
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

    // assert!(get 0 l == 2 && get 1 l == 10);
}
