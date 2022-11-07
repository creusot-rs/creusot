use crate::{std::ops::Index, *};
use crate::prusti_prelude::logic as prusti_logic;

#[cfg_attr(feature = "contracts", creusot::builtins = "seq.Seq.seq")]
pub struct Seq<T: ?Sized>(std::marker::PhantomData<T>);

impl<T> Seq<T> {
    #[cfg(feature = "contracts")]
    #[trusted]
    #[creusot::builtins = "seq.Seq.empty"]
    pub const EMPTY: Self = { Seq(std::marker::PhantomData) };

    #[prusti_logic(() -> '_)]
    pub fn new() -> Self {
        Self::EMPTY
    }

    #[logic]
    #[creusot::prusti::home_sig="('x, '_) -> '_"] // Hack while we don't support constructors
    pub fn get(self, ix: Int) -> Option<T> {
        if ix < self.len() {
            Some(*self.index(ix))
        } else {
            None
        }
    }

    #[trusted]
    #[prusti_logic(('x, '_, '_) -> 'x)]
    #[creusot::builtins = "seq_ext.SeqExt.subsequence"]
    pub fn subsequence(self, _: Int, _: Int) -> Self {
        absurd
    }

    #[trusted]
    #[prusti_logic(('x) -> 'x)]
    #[creusot::builtins = "seq.Seq.singleton"]
    pub fn singleton(_: T) -> Self {
        absurd
    }

    #[prusti_logic(('x) -> 'x)]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len())
    }

    #[prusti_logic(('x) -> 'x)]
    pub fn upto_last(self) -> Seq<T> {
        self.subsequence(0, self.len() - 1)
    }

    #[prusti_logic(('x) -> 'x)]
    pub fn last(self) -> T {
        self[self.len() - 1]
    }

    #[prusti_logic(('x) -> 'x)]
    pub fn head(self) -> T {
        self[0]
    }

    #[trusted]
    #[prusti_logic(('_) -> '_)]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len(self) -> Int {
        absurd
    }

    #[trusted]
    #[prusti_logic(('x, '_, 'x) -> 'x)]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, _: Int, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[prusti_logic(('_, '_) -> '_)]
    #[creusot::builtins = "seq.Seq.(==)"]
    pub fn ext_eq(self, _: Self) -> bool {
        absurd
    }

    #[trusted]
    #[prusti_logic(('x, 'x) -> 'x)]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push(self, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[prusti_logic(('x, 'x) -> 'x)]
    #[creusot::builtins = "seq.Seq.(++)"]
    pub fn concat(self, _: Self) -> Self {
        absurd
    }

    #[predicate]
    pub fn permutation_of(self, o: Self) -> bool {
        self.permut(o, 0, self.len())
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "seq.Permut.permut"]
    pub fn permut(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "seq.Permut.exchange"]
    pub fn exchange(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[predicate]
    pub fn contains(self, e: T) -> bool {
        pearlite! { exists<i : Int> 0 <= i &&  i <self.len() && self[i] == e }
    }

    // A hack to trigger loading the `seq.FreeMonoid` module which is quite useful
    #[logic]
    #[creusot::builtins = "seq.FreeMonoid.left_neutral"]
    pub fn left_neutral(self) {}
}

// A hack which allows us to use [..] notation for sequences.
// Relies on the fact we don't enforce that implementations of traits are of
// the same function type as the trait signature.. When this is addressed
// the following instance will error.
#[cfg(feature = "contracts")]
impl<T> std::ops::Index<Int> for Seq<T> {
    type Output = T;

    #[trusted]
    #[prusti_logic((r'x, '_) -> r'x)]
    #[creusot::builtins = "seq.Seq.get"]
    fn index(&self, _: Int) -> &T {
        absurd
    }
}
