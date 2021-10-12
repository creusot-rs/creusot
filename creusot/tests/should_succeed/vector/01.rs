#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::*;

struct MyVec<T>(Vec<T>);

pub struct GhostRecord<T>
where
    T: ?Sized;

impl<T> Model for GhostRecord<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> GhostRecord<T> {
    #[trusted]
    #[ensures(@result === *a)]
    fn record(a: &T) -> GhostRecord<T> {
        GhostRecord::<T>
    }
}

impl<T: ?Sized> Model for MyVec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> MyVec<T> {
    #[trusted]
    #[ensures(@result === (@self).len())]
    fn len(&self) -> usize {
        self.0.len()
    }

    #[trusted]
    #[ensures(match result {
        Some(t) => *t === (@*self).index(ix.into()),
        None => (@*self).len() <= ix.into(),
    })]
    fn get(&self, ix: usize) -> Option<&T> {
        self.0.get(ix)
    }

    #[trusted]
    #[ensures(@^self === (@self).push(v))]
    fn push(&mut self, v: T) {
        self.0.push(v)
    }

    #[trusted]
    #[requires(@ix < (@self).len())]
    #[ensures(*result === (@self).index(@ix))]
    fn index(&self, ix: usize) -> &T {
        use std::ops::Index;
        self.0.index(ix)
    }

    #[trusted]
    #[requires(@ix < (@self).len())]
    #[ensures(*result === (@self).index(@ix))]
    #[ensures(^result === (@^self).index(@ix))]
    #[ensures(forall<j: Int> 0 <= j && j <= (@^self).len() ==>
        !(j === @ix) ==>
        (@^self).index(j) === (@self).index(j))]
    #[ensures((@self).len() === (@^self).len())]
    fn index_mut(&mut self, ix: usize) -> &mut T {
        use std::ops::IndexMut;
        self.0.index_mut(ix)
    }
}

#[ensures(forall<i: Int> 0 <= i && i < (@^v).len() ==> (@^v).index(i) === 0u32)]
#[ensures((@v).len() === (@^v).len())]
fn all_zero(v: &mut MyVec<u32>) {
    let mut i = 0;
    let old_v: GhostRecord<&mut MyVec<u32>> = GhostRecord::record(&v);
    // This invariant is because why3 can't determine that the prophecy isn't modified by the loop
    // Either Why3 or Creusot should be improved to do this automaticallly (probably why3)
    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(in_bounds, (@v).len() === (@@old_v).len())]
    #[invariant(all_zero, forall<j: Int> 0 <= j && j < @i ==> (@v).index(j) === 0u32)]
    while i < v.len() {
        *v.index_mut(i) = 0;
        i += 1;
    }
}

fn main() {}
