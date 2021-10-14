use creusot_contracts::*;

pub struct Vec<T>(std::vec::Vec<T>);

pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[ensures(@result === *a)]
    pub fn record(a: &T) -> Ghost<T> {
        panic!()
    }
}

impl<T: ?Sized> Model for Vec<T> {
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
        Some(t) => *t === (@*self).index(ix.into()),
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
    #[ensures(*result === (@self).index(@ix))]
    pub fn index(&self, ix: usize) -> &T {
        use std::ops::Index;
        self.0.index(ix)
    }

    #[trusted]
    #[requires(@ix < (@*self).len())]
    #[ensures(*result === (@self).index(ix.into()))]
    #[ensures(^result === (@^self).index(ix.into()))]
    #[ensures(forall<j : Int> 0 <= j && j <= (@^self).len() ==>
        !(j === @ix) ==>
        (@^self).index(j) === (@*self).index(j))]
    #[ensures((@*self).len() === (@^self).len())]
    pub fn index_mut(&mut self, ix: usize) -> &mut T {
        use std::ops::IndexMut;
        self.0.index_mut(ix)
    }
}
