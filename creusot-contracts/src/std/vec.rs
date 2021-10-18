use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::{Int, Model, Seq};
pub struct Vec<T>(std::vec::Vec<T>);

impl<T> Model for Vec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Vec<T> {
    #[trusted]
    #[ensures(result.into() === (@self).len())]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[trusted]
    #[ensures(match result {
        Some(t) => *t === (@*self)[ix.into()],
        None => (@*self).len() <= ix.into(),
    })]
    pub fn get(&self, ix: usize) -> Option<&T> {
        self.0.get(ix)
    }

    #[trusted]
    #[ensures(@^self === (@self).push(v))]
    pub fn push(&mut self, v: T) {
        self.0.push(v)
    }

    #[trusted]
    #[requires(@ix < (@self).len())]
    #[ensures(*result === (@self)[@ix])]
    pub fn index(&self, ix: usize) -> &T {
        use std::ops::Index;
        self.0.index(ix)
    }

    #[trusted]
    #[requires(@ix < (@*self).len())]
    #[ensures(*result === (@self)[@ix])]
    #[ensures(^result === (@^self)[@ix])]
    #[ensures(forall<j : Int> 0 <= j && j <= (@^self).len() ==>
        !(j === @ix) ==>
        (@^self)[j] === (@*self)[j])]
    #[ensures((@*self).len() === (@^self).len())]
    pub fn index_mut(&mut self, ix: usize) -> &mut T {
        use std::ops::IndexMut;
        self.0.index_mut(ix)
    }

    #[trusted]
    #[requires(@i < (@self).len())]
    #[requires(@j < (@self).len())]
    #[ensures((@^self)[@i] === (@*self)[@j])]
    #[ensures((@^self)[@j] === (@*self)[@i])]
    #[ensures(forall<k : Int> 0 <= k && k <= (@^self).len() && @i != k && @j != k ==>
        (@^self)[k] === (@*self)[k]
    )]
    #[ensures((@^self).len() === (@*self).len())]
    pub fn swap(&mut self, i: usize, j: usize) {
        self.0.swap(i, j)
    }

    pub fn last(&mut self) -> Option<&T> {
        self.0.last()
    }
}
