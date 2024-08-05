use ::std::marker::PhantomData;
use creusot_contracts::{
    logic::{IndexLogic, Mapping},
    *,
};

#[trusted]
pub struct Seq<T: ?Sized>(PhantomData<T>);

impl<T> Seq<T> {
    #[trusted]
    #[open(self)]
    #[logic]
    pub fn any_elt() -> T {
        absurd
    }

    #[cfg(creusot)]
    #[trusted]
    pub const EMPTY: Self = { Seq(PhantomData) };

    #[law]
    #[trusted]
    #[open(self)]
    #[ensures(Self::EMPTY.len() == 0)]
    #[ensures(Self::EMPTY.view() == Mapping::cst(Self::any_elt()))]
    pub fn empty_spec() {}

    #[law]
    #[trusted]
    #[open]
    #[ensures(forall<s: Self> s == Seq::new_raw(s.len(), s.view()))]
    pub fn new_raw_spec() {}

    #[logic]
    #[trusted]
    #[open(self)]
    #[requires(len >= 0)]
    #[requires(forall<i: Int> i < 0 || i >= len ==> data.get(i) == Self::any_elt())]
    #[ensures(result.len() == len)]
    #[ensures(result.view() == data)]
    pub fn new_raw(len: Int, data: Mapping<Int, T>) -> Self {
        pearlite! {absurd}
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
    #[ensures(forall<i: Int>  i < 0 || i >= self.len() ==> result.get(i) == Self::any_elt())]
    pub fn view(self) -> Mapping<Int, T> {
        pearlite! {absurd}
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(forall<i: Int> result.get(i) == if 0 <= i && i < len {data.get(i)} else {Self::any_elt()})]
    pub fn new_view(len: Int, data: Mapping<Int, T>) -> Mapping<Int, T> {
        pearlite! {absurd}
    }

    #[logic]
    #[open(self)]
    #[requires(len >= 0)]
    #[ensures(result.len() == len)]
    #[ensures(result.view() == Self::new_view(len, data))]
    pub fn new(len: Int, data: Mapping<Int, T>) -> Self {
        Self::new_raw(len, Self::new_view(len, data))
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
    #[ensures(forall<i: Int> result.get(i) == if 0 <= i && i < m - n {self[i + n]} else {Self::any_elt()})]
    pub fn subsequence_view(self, n: Int, m: Int) -> Mapping<Int, T> {
        pearlite! {absurd}
    }

    #[logic]
    #[open(self)]
    #[requires(0 <= n && n <= m && m <= self.len())]
    #[ensures(result.len() == m - n)]
    #[ensures(result.view() == self.subsequence_view(n, m))]
    pub fn subsequence(self, n: Int, m: Int) -> Self {
        Seq::new_raw(m - n, self.subsequence_view(n, m))
    }

    #[logic]
    #[open(self)]
    #[ensures(result.len() == 1)]
    #[ensures(result.view() == Mapping::cst(Self::any_elt()).set(0, v))]
    pub fn singleton(v: T) -> Self {
        Self::new_raw(1, Mapping::cst(Self::any_elt()).set(0, v))
    }

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len())
    }

    #[logic]
    #[open(self)]
    #[requires(0 <= j && j < self.len())]
    #[ensures(result.len() == self.len())]
    #[ensures(result.view() == self.view().set(j, v))]
    pub fn set(self, j: Int, v: T) -> Self {
        Self::new_raw(self.len(), self.view().set(j, v))
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
    #[open(self)]
    #[ensures(result.len() == self.len() + 1)]
    #[ensures(result.view() == self.view().set(self.len(), v))]
    pub fn push(self, v: T) -> Self {
        self.concat(Self::singleton(v))
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(forall<i: Int> result.get(i) == if i < self.len() {self[i]} else {other[i - self.len()]})]
    pub fn concat_view(self, other: Self) -> Mapping<Int, T> {
        pearlite! {absurd}
    }

    #[logic]
    #[open(self)]
    #[ensures(result.len() == self.len() + other.len())]
    #[ensures(result.view() == self.concat_view(other))]
    pub fn concat(self, other: Self) -> Self {
        Self::new_raw(self.len() + other.len(), self.concat_view(other))
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(forall<i: Int> result.get(i) == self[self.len() - 1 - i])]
    pub fn reverse_view(self) -> Mapping<Int, T> {
        pearlite! { absurd }
    }

    #[logic]
    #[open(self)]
    #[ensures(result.len() == self.len())]
    #[ensures(result.view() == self.reverse_view())]
    pub fn reverse(self) -> Self {
        Self::new_raw(self.len(), self.reverse_view())
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
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, i: Int) -> Self::Item {
        self.view().get(i)
    }
}
