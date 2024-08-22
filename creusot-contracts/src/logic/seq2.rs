use crate::{logic::mapping::Mapping, *};
use ::std::marker::PhantomData;
use creusot_contracts::logic::IndexLogic;

#[trusted]
pub struct Seq<T: ?Sized>(PhantomData<T>);

impl<T> Seq<T> {
    #[cfg(creusot)]
    #[trusted]
    pub const EMPTY: Self = { Seq(PhantomData) };

    #[law]
    #[trusted]
    #[open(self)]
    #[ensures(Self::EMPTY.len() == 0)]
    pub fn empty_len() {}

    #[logic]
    #[trusted]
    #[open(self)]
    #[requires(len >= 0)]
    #[ensures(result.len() == len)]
    #[ensures(forall<i : Int> 0 <= i && i < result.len() ==> result[i] == data.get(i))]
    pub fn new(len: Int, data: Mapping<Int, T>) -> Self {
        pearlite! {absurd}
    }

    #[logic]
    #[open]
    pub fn get(self, ix: Int) -> Option<T> {
        if 0 <= ix && ix < self.len() {
            Some(self.index_logic(ix))
        } else {
            None
        }
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[requires(0 <= n && n <= m && m <= self.len())]
    #[ensures(result.len() == m - n)]
    #[ensures(forall<i : Int> 0 <= i && i < result.len() ==> result[i] == self[n + i])]
    pub fn subsequence(self, n: Int, m: Int) -> Self {
        pearlite! {absurd}
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result.len() == 1)]
    #[ensures(result[0] == v)]
    pub fn singleton(v: T) -> Self {
        pearlite! {absurd}
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len())
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result >= 0)]
    pub fn len(self) -> Int {
        pearlite! {absurd}
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[requires(0 <= j && j < self.len())]
    #[ensures(result.len() == self.len())]
    #[ensures(result[j] == v)]
    #[ensures(forall<i : Int> 0 <= i && i < result.len() && i != j ==> result[i] == self[i])]
    pub fn set(self, j: Int, v: T) -> Self {
        pearlite! {absurd}
    }

    #[predicate]
    #[trusted]
    #[open(self)]
    #[ensures(result ==> self == oth)]
    #[ensures(self.len() == oth.len() &&
    (forall<i : Int> 0 <= i && i < self.len() ==> self[i] == oth[i]) ==> result)]
    pub fn ext_eq(self, oth: Self) -> bool {
        pearlite! {absurd}
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn push(self, v: T) -> Self {
        self.concat(Self::singleton(v))
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result.len() == self.len() + other.len())]
    #[ensures(forall<i : Int> 0 <= i && i < result.len() ==> result[i] ==
    if i < self.len() {self[i]} else {other[i - self.len()]})]
    pub fn concat(self, other: Self) -> Self {
        pearlite! {absurd}
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<i : Int> 0 <= i && i < result.len() ==> result[i] == self[self.len() - 1 - i])]
    pub fn reverse(self) -> Self {
        pearlite! {absurd}
    }

    // #[predicate]
    // #[open]
    // pub fn permutation_of(self, o: Self) -> bool {
    //     self.permut(o, 0, self.len())
    // }
    //
    // #[predicate]
    // #[open]
    // pub fn permut(self, _: Self, _: Int, _: Int) -> bool {
    //
    // }

    #[open]
    #[predicate]
    pub fn exchange(self, oth: Self, i: Int, j: Int) -> bool {
        self.len() == oth.len()
            && 0 <= i
            && i < self.len()
            && 0 <= j
            && j < self.len()
            && self[i] == oth[j]
            && self[j] == oth[i]
            && pearlite! {forall<k: Int> 0 <= k && k < self.len() ==> k != i ==> k != j ==> self[k] == oth[k]}
    }

    #[open]
    #[predicate]
    pub fn contains(self, e: T) -> bool {
        pearlite! { exists<i : Int> 0 <= i &&  i <self.len() && self[i] == e }
    }

    #[open]
    #[predicate]
    pub fn sorted_range(self, l: Int, u: Int) -> bool
    where
        T: OrdLogic,
    {
        pearlite! {
            forall<i : Int, j : Int> l <= i && i <= j && j < u ==> self[i] <= self[j]
        }
    }

    #[open]
    #[predicate]
    pub fn sorted(self) -> bool
    where
        T: OrdLogic,
    {
        self.sorted_range(0, self.len())
    }
}

impl<T> Seq<&T> {
    #[logic]
    #[trusted]
    #[open(self)]
    #[creusot::builtins = "prelude.prelude.Cast.id"]
    pub fn to_owned_seq(self) -> Seq<T> {
        pearlite! {absurd}
    }
}

impl<T> IndexLogic<Int> for Seq<T> {
    type Item = T;

    #[logic]
    #[trusted]
    #[open(self)]
    fn index_logic(self, _: Int) -> Self::Item {
        pearlite! {absurd}
    }
}
