use crate::{logic::Mapping, util::*, *};

type PMap<K, V> = Mapping<K, Option<SizedW<V>>>;

#[trusted] //opaque
pub struct FMap<K, V: ?Sized>(PMap<K, V>);

impl<K, V: ?Sized> FMap<K, V> {
    #[trusted]
    #[ghost]
    #[open(self)]
    #[ensures(result >= 0)]
    pub fn len(self) -> Int {
        absurd
    }

    #[trusted]
    #[ghost]
    #[open(self)]
    pub fn mk(_m: PMap<K, V>) -> Self {
        absurd
    }

    #[trusted]
    #[open(self)]
    #[ghost]
    #[ensures(Self::mk(result) == self)] // injectivity
    pub fn view(self) -> PMap<K, V> {
        absurd
    }

    #[trusted]
    #[open(self)]
    #[ghost]
    #[ensures(result.view() == self.view().set(k, Some(v.make_sized())))]
    #[ensures(self.contains(k) ==> result.len() == self.len())]
    #[ensures(!self.contains(k) ==> result.len() == self.len() + 1)]
    pub fn insert(self, k: K, v: V) -> Self {
        absurd
    }

    #[trusted]
    #[open(self)]
    #[ghost]
    #[ensures(result.view() == self.view().set(k, None))]
    #[ensures(result.len() == if self.contains(k) {self.len() - 1} else {self.len()})]
    pub fn remove(self, k: K) -> Self {
        absurd
    }

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn get(self, k: K) -> Option<SizedW<V>> {
        self.view().get(k)
    }

    #[ghost]
    #[open]
    pub fn lookup_unsized(self, k: K) -> SizedW<V> {
        unwrap(self.get(k))
    }

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    pub fn lookup(self, k: K) -> V
    where
        V: Sized,
    {
        *self.lookup_unsized(k)
    }

    #[ghost]
    #[open]
    pub fn contains(self, k: K) -> bool {
        self.get(k) != None
    }

    #[trusted]
    #[ghost]
    #[open(self)]
    #[ensures(result.len() == 0)]
    #[ensures(result.view() == Mapping::cst(None))]
    pub fn empty() -> Self {
        absurd
    }

    #[ghost]
    #[open]
    pub fn is_empty(self) -> bool {
        self.ext_eq(FMap::empty())
    }

    #[ghost]
    #[open]
    pub fn disjoint(self, other: Self) -> bool {
        pearlite! {forall<k: K> !self.contains(k) || !other.contains(k)}
    }

    #[ghost]
    #[open]
    pub fn subset(self, other: Self) -> bool {
        pearlite! {forall<k: K> self.contains(k) ==> other.get(k) == self.get(k)}
    }

    #[trusted]
    #[ghost]
    #[open(self)]
    #[requires(self.disjoint(other))]
    #[ensures(forall<k: K> result.get(k) == if self.contains(k) {
        self.get(k)
    } else if other.contains(k) {
        other.get(k)
    } else {
        None
    })]
    #[ensures(result.len() == self.len() + other.len())]
    pub fn union(self, other: Self) -> Self {
        absurd
    }

    #[trusted]
    #[ghost]
    #[open(self)]
    #[ensures(forall<k: K> result.get(k) == if other.contains(k) {None} else {self.get(k)})]
    pub fn subtract_keys(self, other: Self) -> Self {
        absurd
    }

    #[ghost]
    #[open]
    #[requires(other.subset(self))]
    #[ensures(result.disjoint(other))]
    #[ensures(other.union(result).ext_eq(self))]
    pub fn subtract(self, other: Self) -> Self {
        self.subtract_keys(other)
    }

    #[ghost]
    #[open]
    #[ensures(result ==> self == other)]
    #[ensures((forall<k: K> self.get(k) == other.get(k)) ==> result)]
    pub fn ext_eq(self, other: Self) -> bool {
        self.view() == other.view()
    }
}
