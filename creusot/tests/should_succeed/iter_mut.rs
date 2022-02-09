// UNBOUNDED WHY3PROVE Z3
#![feature(type_ascription, box_syntax)]

extern crate creusot_contracts;

use creusot_contracts::*;

// We don't yet use the standard vec because we provide the non-standard `iter_mut` method.
struct Vec<T>(std::vec::Vec<T>);

impl<T> Model for Vec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        std::process::abort()
    }
}

impl<T> Vec<T> {
    // Needs ensure that the result of self is the results of itermut
    #[trusted]
    #[ensures((@*self).len() === (@result).len() && (@*self).len() === (@^self).len())]
    #[ensures(forall<i : Int> 0 <= i && i <= (@*self).len() ==> (@*self)[i] === *(@result)[i])]
    #[ensures(forall<i : Int> 0 <= i && i <= (@^self).len() ==> (@^self)[i] === ^(@result)[i])]
    fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut(self.0.iter_mut())
    }

    #[trusted]
    #[ensures(result.into() === (@*self).len())]
    fn len(&self) -> usize {
        self.0.len()
    }
}

struct IterMut<'a, T>(std::slice::IterMut<'a, T>);

impl<'a, T> Model for IterMut<'a, T> {
    type ModelTy = Seq<&'a mut T>;

    #[trusted]
    #[logic]
    fn model(self) -> Self::ModelTy {
        std::process::abort()
    }
}

impl<'a, T> IterMut<'a, T> {
    #[trusted]
    #[ensures(result === (@*self).get(0))]
    #[ensures(@^self === (@*self).tail())]
    fn next(&mut self) -> Option<&'a mut T> {
        self.0.next()
    }
}

#[ensures((@^v).len() === (@v).len())]
#[ensures(forall<i : Int> 0 <= i && i < (@^v).len() ==> @(@^v)[i] === @(@v)[i] + 5)]
fn inc_vec(v: &mut Vec<u32>) {
    let old_v = Ghost::record(&v);

    let mut it = v.iter_mut();
    let mut _ghost_seen: usize = 0; // Creusot doesn't yet have ghost code
    #[invariant(incremented, forall<i : Int>
        0 <= i && i < @_ghost_seen ==>
        @(@^@old_v)[i] === @(@@old_v)[i] + 5
    )]
    #[invariant(to_come, forall<i : Int> 0 <= i && i < (@it).len() ==>
        *(@it)[i] === (@@old_v)[i + @_ghost_seen] && ^(@it)[i] === (@^@old_v)[i + @_ghost_seen]
    )]
    #[invariant(_ghost_seen, @_ghost_seen + (@it).len() === (@@old_v).len())]
    while let Some(r) = it.next() {
        *r += 5;
        _ghost_seen += 1;
    }
}
