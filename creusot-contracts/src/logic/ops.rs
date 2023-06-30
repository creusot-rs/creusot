use crate::*;

pub trait IndexLogic<I> {
    type Item;

    #[logic]
    fn index_logic(self, idx: I) -> Self::Item;
}

impl<T, S: ShallowModel<ShallowModelTy = Seq<T>> + ?Sized> IndexLogic<Int> for S {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, S: ShallowModel<ShallowModelTy = Seq<T>> + ?Sized> IndexLogic<usize> for S {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> IndexLogic<Int> for Ghost<Seq<T>> {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { (*self)[ix] }
    }
}
