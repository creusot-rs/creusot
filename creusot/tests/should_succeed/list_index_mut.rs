extern crate creusot_contracts;

use creusot_contracts::*;

enum Option<T> {
    None,
    Some(T),
}

use Option::*;

pub struct List(u32, Option<Box<List>>);

#[logic]
fn len(l: List) -> Int {
    {
        let List(_, ls) = l;
        1 + match ls {
            Some(ls) => len(*ls),
            None => 0,
        }
    }
}

#[logic]
fn get(l: List, ix: Int) -> Option<u32> {
    {
        let List(i, ls) = l;
        match ix > 0 {
            false => Some(i),
            true => match ls {
                Some(ls) => get(*ls, ix - 1),
                None => None,
            },
        }
    }
}

#[requires(@param_ix < len(*param_l))]
#[ensures(Some(*result) == get(*param_l, @param_ix))]
#[ensures(Some(^result) == get(^param_l, @param_ix))]
#[ensures(len(^param_l) == len(*param_l))]
#[ensures(forall<i:Int> 0 <= i && i < len(*param_l) && i != (@param_ix) ==> get(*param_l, i) == get(^param_l, i))]
pub fn index_mut(param_l: &mut List, param_ix: usize) -> &mut u32 {
    let mut l = param_l;
    let mut ix = param_ix;
    #[invariant(valid_ix, 0usize <= ix && @ix < len (*l))]
    #[invariant(get_target_now, get(*l, @ix) == get(*param_l, @param_ix))]
    #[invariant(get_target_fin, get(^l, @ix) == get(^param_l, @param_ix))]
    #[invariant(len, len(^l) == len(*l) ==> len(^param_l) == len(*param_l))]
    #[invariant(untouched,
        (forall<i:Int> 0 <= i && i < len (*l) && i != @ix ==> get(^l, i) == get(*l, i)) ==>
        forall<i:Int> 0 <= i && i < len (*param_l) && i != @param_ix ==>
            get (^param_l, i) == get (*param_l, i)
    )]
    while ix > 0 {
        match l.1 {
            Some(ref mut n) => {
                l = n;
            }
            None => std::process::abort(),
        }
        ix -= 1;
    }

    &mut l.0
}

// Ensure that this performs a set on the list
#[requires(@ix < len(*l))]
#[ensures(Some(v) == get(^l, @ix))]
#[ensures(len(^l) == len(*l))]
#[ensures(forall<i:Int> 0 <= i && i < len(*l) && i != @ix ==> get(*l, i) == get(^l, i))]
pub fn write(l: &mut List, ix: usize, v: u32) {
    *index_mut(l, ix) = v;
}

pub fn f() {
    let mut l = List(1, Some(Box::new(List(10, None))));
    write(&mut l, 0, 2);

    // assert!(get 0 l == 2 && get 1 l == 10);
}
