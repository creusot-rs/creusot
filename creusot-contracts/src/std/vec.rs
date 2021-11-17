use crate as creusot_contracts;
use crate::logic::*;
use crate::{std::clone::Clone, Int, Model, Seq};
use creusot_contracts_proc::*;

#[trusted]
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
    #[ensures((@result).len() === 0)]
    pub fn new() -> Self {
        Vec(std::vec::Vec::new())
    }

    #[trusted]
    #[ensures((@result).len() === 0)]
    pub fn with_capacity(capacity: usize) -> Vec<T> {
        Vec(std::vec::Vec::with_capacity(capacity))
    }

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
    #[requires(@i < (@self).len())]
    #[requires(@j < (@self).len())]
    #[ensures((@^self).exchange(@*self, @i, @j))]
    pub fn swap(&mut self, i: usize, j: usize) {
        self.0.swap(i, j)
    }

    #[trusted]
    #[ensures(match result {
        Some(t) => (@self) === (@^self).push(t),
        None => (@self).len() === (@^self).len() && (@self).len() === 0
    })]
    pub fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }
}

impl<T> std::ops::IndexMut<usize> for Vec<T> {
    #[trusted]
    #[requires(@ix < (@*self).len())]
    #[ensures(*result === (@self)[@ix])]
    #[ensures(^result === (@^self)[@ix])]
    #[ensures(forall<j : Int> 0 <= j && j < (@^self).len() ==>
        !(j === @ix) ==>
        (@^self)[j] === (@*self)[j])]
    #[ensures((@*self).len() === (@^self).len())]
    fn index_mut(&mut self, ix: usize) -> &mut T {
        self.0.index_mut(ix)
    }
}

impl<T> std::ops::Index<usize> for Vec<T> {
    type Output = T;

    #[trusted]
    #[requires(@ix < (@self).len())]
    #[ensures(*result === (@self)[@ix])]
    fn index(&self, ix: usize) -> &T {
        self.0.index(ix)
    }
}

impl<T: Clone> Clone for Vec<T> {
    #[trusted]
    fn clone(&self) -> Self {
        panic!()
        // Vec(self.0.iter().map(|r : &T| r.clone()).collect())
    }
}

unsafe impl<T: Resolve> Resolve for Vec<T> {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! { forall<i : Int> 0 <= i && i < (@self).len() ==> (@self)[i].resolve() }
    }
}

#[trusted]
#[ensures((@result).len() === @n)]
#[ensures(forall<i : Int> 0 <= i && i < @n ==> (@result)[i] === elem)]
pub fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T> {
    panic!()
}
