use crate::{logic::Mapping, util::*, *};

pub struct FMap<K, V: ?Sized>(pub Mapping<K, Option<SizedW<V>>>);

#[trusted]
#[logic]
#[ensures((forall<k: K> m.0.get(k) == None) ==> m.len() == 0)]
fn len_def0<K, V: ?Sized>(m: FMap<K, V>) -> bool {
    true
}

#[trusted]
#[logic]
#[ensures(m.0.get(k) != None ==> m.len() == FMap(m.0.set(k, None)).len() + 1)]
fn len_def1<K, V: ?Sized>(m: FMap<K, V>, k: K) -> bool {
    true
}

impl<K, V: ?Sized> FMap<K, V> {
    #[trusted]
    #[logic]
    #[ensures(result >= 0)]
    pub fn len(self) -> Int {
        absurd
    }

    #[logic]
    #[ensures(self.contains(k) ==> result.len() == self.len())]
    #[ensures(!self.contains(k) ==> result.len() == self.len() + 1)]
    pub fn insert(self, k: K, v: V) -> Self {
        FMap(self.0.set(k, Some(v.make_sized()))).remove(k).ext_eq(self.remove(k));
        FMap(self.0.set(k, Some(v.make_sized())))
    }

    #[logic]
    #[ensures(result.len() == if self.contains(k) {self.len() - 1} else {self.len()})]
    pub fn remove(self, k: K) -> Self {
        len_def1(self, k);
        FMap(self.0.set(k, None))
    }

    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn get(self, k: K) -> Option<SizedW<V>> {
        self.0.get(k)
    }

    #[logic]
    pub fn lookup_unsized(self, k: K) -> SizedW<V> {
        unwrap(self.0.get(k))
    }

    #[logic]
    pub fn lookup(self, k: K) -> V
    where
        V: Sized,
    {
        *unwrap(self.0.get(k))
    }

    #[logic]
    pub fn contains(self, k: K) -> bool {
        self.0.get(k) != None
    }

    #[logic]
    #[ensures(result.len() == 0)]
    pub fn empty() -> Self {
        len_def0(FMap::<K, V>(Mapping::cst(None)));
        FMap(Mapping::cst(None))
    }

    #[logic]
    pub fn is_empty(self) -> bool {
        self.ext_eq(FMap::empty())
    }

    #[logic]
    pub fn disjoint(self, other: Self) -> bool {
        pearlite! {forall<k: K> !self.contains(k) || !other.contains(k)}
    }

    #[logic]
    pub fn subset(self, other: Self) -> bool {
        pearlite! {forall<k: K> self.contains(k) ==> other.get(k) == self.get(k)}
    }

    #[trusted]
    #[logic]
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
    #[logic]
    #[ensures(forall<k: K> result.get(k) == if other.contains(k) {None} else {self.get(k)})]
    pub fn subtract_keys(self, other: Self) -> Self {
        absurd
    }

    #[logic]
    #[requires(other.subset(self))]
    #[ensures(result.disjoint(other))]
    #[ensures(other.union(result).ext_eq(self))]
    pub fn subtract(self, other: Self) -> Self {
        self.subtract_keys(other)
    }

    #[logic]
    #[ensures(result ==> self == other)]
    #[ensures((forall<k: K> self.0.get(k) == other.0.get(k)) ==> result)]
    pub fn ext_eq(self, other: Self) -> bool {
        self.0 == other.0
    }
}
