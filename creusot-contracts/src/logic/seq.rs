use crate::{
    invariant::*,
    logic::{ops::IndexLogic, Mapping},
    *,
};

#[trusted]
#[cfg_attr(creusot, creusot::builtins = "seq.Seq.seq")]
pub struct Seq<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> Seq<T> {
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "seq.Seq.empty"]
    pub const EMPTY: Self = { Seq(std::marker::PhantomData) };

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.create"]
    pub fn new(_: Int, _: Mapping<Int, T>) -> Self {
        absurd
    }

    #[logic]
    #[open]
    pub fn get(self, ix: Int) -> Option<T>
    where
        T: Sized, // TODO : don't require this (problem: return type needs to be sized)
    {
        if 0 <= ix && ix < self.len() {
            Some(self.index_logic(ix))
        } else {
            None
        }
    }

    #[trusted]
    #[logic]
    #[open]
    #[creusot::builtins = "seq.Seq.get"]
    pub fn index_logic_unsized(self, _: Int) -> Box<T> {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "prelude.seq_ext.SeqExt.subsequence"]
    pub fn subsequence(self, _: Int, _: Int) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.singleton"]
    pub fn singleton(_: T) -> Self {
        absurd
    }

    #[logic]
    #[open]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len())
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[rustc_diagnostic_item = "seq_len"]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len(self) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, _: Int, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.(==)"]
    pub fn ext_eq(self, _: Self) -> bool {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push(self, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.(++)"]
    pub fn concat(self, _: Self) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Reverse.reverse"]
    pub fn reverse(self) -> Self {
        absurd
    }

    #[predicate]
    #[open]
    pub fn permutation_of(self, o: Self) -> bool {
        self.permut(o, 0, self.len())
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Permut.permut"]
    pub fn permut(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Permut.exchange"]
    pub fn exchange(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[open]
    #[predicate]
    pub fn contains(self, e: T) -> bool
    where
        T: Sized, // TODO : don't require this (problem: uses index)
    {
        pearlite! { exists<i : Int> 0 <= i &&  i < self.len() && self[i] == e }
    }

    #[open]
    #[predicate]
    pub fn sorted_range(self, l: Int, u: Int) -> bool
    where
        T: OrdLogic + Sized, // TODO : don't require this (problem: uses index)
    {
        pearlite! {
            forall<i : Int, j : Int> l <= i && i <= j && j < u ==> self[i] <= self[j]
        }
    }

    #[open]
    #[predicate]
    pub fn sorted(self) -> bool
    where
        T: OrdLogic + Sized, // TODO : don't require this (problem: uses index)
    {
        self.sorted_range(0, self.len())
    }
}

impl<T: ?Sized> Seq<&T> {
    #[logic]
    #[open]
    #[trusted]
    #[creusot::builtins = "prelude.prelude.Seq.to_owned"]
    pub fn to_owned_seq(self) -> Seq<T> {
        pearlite! {absurd}
    }
}

impl<T> IndexLogic<Int> for Seq<T> {
    type Item = T;

    #[logic]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "seq_index"]
    #[creusot::builtins = "seq.Seq.get"]
    fn index_logic(self, _: Int) -> Self::Item {
        absurd
    }
}

impl<T: ?Sized> Invariant for Seq<T> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    fn invariant(self) -> bool {
        pearlite! { forall<i:Int> 0 <= i && i < self.len() ==> inv(self.index_logic_unsized(i)) }
    }
}

#[trusted]
impl<T: ?Sized> Resolve for Seq<T> {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        pearlite! { forall<i:Int> 0 <= i && i < self.len() ==> self.index_logic_unsized(i).resolve() }
    }
}
