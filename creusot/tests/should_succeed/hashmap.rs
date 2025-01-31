// UNSTABLE
extern crate creusot_contracts;
use creusot_contracts::{
    invariant::{inv, Invariant},
    logic::{Int, Mapping},
    vec, *,
};

enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T: Clone> Clone for List<T> {
    #[trusted]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        use List::*;
        match self {
            Nil => Nil,
            Cons(t, tl) => Cons(Clone::clone(t), Box::new(Clone::clone(&*tl))),
        }
    }
}

impl<K: DeepModel, V> List<(K, V)> {
    #[logic]
    #[open]
    pub fn get(self, index: K::DeepModelTy) -> Option<V> {
        pearlite! {
            match self {
                List::Nil => None,
                List::Cons((k,v),tl) => if k.deep_model() == index { Some(v) } else { tl.get(index) }
            }
        }
    }

    #[predicate]
    fn no_double_binding(self) -> bool {
        pearlite! {
            match self {
                List::Nil => true,
                List::Cons((k, _), tl) => tl.get(k.deep_model()) == None && tl.no_double_binding()
            }
        }
    }
}

impl<K: DeepModel, V> Resolve for List<(K, V)> {
    #[open(self)]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        // FIXME: we don't resolve keys because we only have access to their deep model.
        pearlite! {
            forall<k: K::DeepModelTy> resolve(&self.get(k))
        }
    }

    #[open(self)]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

// A slightly simplified version of the Rust hashing mechanisms, this sufficiently captures the behavior though
trait Hash: DeepModel {
    #[ensures(result@ == Self::hash_log(self.deep_model()))]
    fn hash(&self) -> u64;

    #[logic]
    fn hash_log(_: Self::DeepModelTy) -> Int;
}

impl Hash for usize {
    #[ensures(result@ == Self::hash_log(self.deep_model()))]
    fn hash(&self) -> u64 {
        *self as u64
    }

    #[logic]
    fn hash_log(x: Int) -> Int {
        pearlite! { x }
    }
}

struct MyHashMap<K, V> {
    buckets: Vec<List<(K, V)>>,
}

impl<K: Hash, V> View for MyHashMap<K, V> {
    type ViewTy = Mapping<K::DeepModelTy, Option<V>>;

    #[open(self)]
    #[logic]
    fn view(self) -> Self::ViewTy {
        |k| self.bucket(k).get(k)
    }
}

impl<K: Hash, V> Resolve for MyHashMap<K, V> {
    #[open(self)]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        // FIXME: we don't resolve keys because we only have access to their deep model.
        pearlite! {
            forall<k: K::DeepModelTy> resolve(&self@.get(k))
        }
    }

    #[open(self)]
    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<K: Hash, V> MyHashMap<K, V> {
    #[logic]
    fn bucket(self, k: K::DeepModelTy) -> List<(K, V)> {
        pearlite! { self.buckets[self.bucket_ix(k)] }
    }

    #[logic]
    fn bucket_ix(self, k: K::DeepModelTy) -> Int {
        pearlite! { K::hash_log(k).rem_euclid(self.buckets@.len()) }
    }

    #[predicate]
    fn good_bucket(self, l: List<(K, V)>, h: Int) -> bool {
        pearlite! {
            forall<k : K::DeepModelTy, v: _> l.get(k) == Some(v) ==> self.bucket_ix(k) == h
        }
    }
}

impl<K: Hash, V> Invariant for MyHashMap<K, V> {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            0 < self.buckets@.len() &&
            forall<i : _> 0 <= i && i < self.buckets@.len() ==> self.good_bucket(self.buckets[i], i) && self.buckets[i].no_double_binding()
        }
    }
}

impl<K: Hash + Copy + Eq + DeepModel, V: Copy> MyHashMap<K, V> {
    #[requires(0 < size@)]
    #[ensures(forall<i: K::DeepModelTy> result@.get(i) == None)]
    pub fn new(size: usize) -> MyHashMap<K, V> {
        let res = MyHashMap { buckets: vec![List::Nil; size] };
        res
    }

    #[ensures(forall<i: K::DeepModelTy> (^self)@.get(i) == (if i == key.deep_model() { Some(val) } else { self@.get(i) } ))]
    pub fn add(&mut self, key: K, val: V) {
        use List::*;
        let old_self = snapshot! { self };
        let length = self.buckets.len();
        let index: usize = key.hash() as usize % length;
        let mut l: &mut List<_> = &mut self.buckets[index];
        let old_l = snapshot! { l };

        #[invariant(inv(l))]
        #[invariant(old_self.good_bucket(*l, index@))]
        #[invariant(old_self.good_bucket(^l, index@) ==> old_self.good_bucket(^old_l.inner(), index@))]
        #[invariant((^l).get(key.deep_model()) == Some(val) ==> (^*old_l).get(key.deep_model()) == Some(val))]
        #[invariant(forall <i:_> (^l).get(i) == (*l).get(i) ==> (^*old_l).get(i) == old_l.get(i))]
        #[invariant((*l).no_double_binding())]
        #[invariant((forall <i:_> (*l).get(i) == (^l).get(i) || i == key.deep_model()) && (^l).no_double_binding() ==>
                      (^*old_l).no_double_binding())]
        while let Cons((k, v), tl) = l {
            let tl = tl;
            if *k == key {
                *v = val;
                return;
            }
            l = &mut **tl;
        }

        *l = Cons((key, val), Box::new(Nil));
    }

    #[ensures(match result {
        Some(v) => self@.get(key.deep_model()) == Some(*v),
        None => self@.get(key.deep_model()) == None,
    })]
    pub fn get(&self, key: K) -> Option<&V> {
        let index: usize = key.hash() as usize % self.buckets.len();
        let mut l = &self.buckets[index];

        #[invariant(inv(l))]
        #[invariant(self.bucket(key.deep_model()).get(key.deep_model()) == (*l).get(key.deep_model()))]
        while let List::Cons((k, v), tl) = l {
            if *k == key {
                return Some(v);
            }
            l = &**tl;
        }
        return None;
    }

    // TODO: Cleanup.
    #[requires(self.buckets@.len() < 1000)]
    #[ensures(forall<k : K::DeepModelTy> (^self)@.get(k) == self@.get(k))] // lets prove the extensional version for now
    #[allow(dead_code)]
    fn resize(&mut self) {
        let old_self = snapshot! { self };
        let mut new = Self::new(self.buckets.len() * 2);

        let mut i: usize = 0;
        #[invariant(inv(self))]
        #[invariant(inv(new))]
        #[invariant(forall<k : K::DeepModelTy> old_self.bucket_ix(k) < i@ ==> old_self@.get(k) == new@.get(k))]
        #[invariant(forall<k : K::DeepModelTy>
            i@ <=   old_self.bucket_ix(k) &&
                    old_self.bucket_ix(k) <= old_self.buckets@.len() ==> new@.get(k) == None
        )]
        #[invariant(forall<j : Int> i@ <= j && j < old_self.buckets@.len() ==> self.buckets[j] == old_self.buckets[j])]
        #[invariant(old_self.buckets@.len() == self.buckets@.len())]
        #[invariant(i@ <= self.buckets@.len())]
        while i < self.buckets.len() {
            let mut l: List<_> = std::mem::replace(&mut self.buckets[i], List::Nil);

            #[invariant(inv(new))]
            #[invariant(inv(l))]
            #[invariant(forall<k : K::DeepModelTy> old_self.bucket_ix(k) < i@ ==> old_self@.get(k) == new@.get(k))]
            #[invariant(forall<k : K::DeepModelTy>
                i@ < old_self.bucket_ix(k) && old_self.bucket_ix(k) <= old_self.buckets@.len()  ==> new@.get(k) == None
            )]
            #[invariant(forall<k : K::DeepModelTy> old_self.bucket_ix(k) == i@ ==>
                        old_self@.get(k) == match l.get(k) { None => new@.get(k), Some(v) => Some(v) })]
            #[invariant(l.no_double_binding())]
            #[invariant(old_self.good_bucket(l, i@))]
            while let List::Cons((k, v), tl) = l {
                new.add(k, v);
                l = *tl;
            }
            proof_assert! { forall<k : K::DeepModelTy> old_self.bucket_ix(k) == i@  ==> old_self@.get(k) == new@.get(k) };
            i += 1;
        }

        *self = new;
    }
}

pub fn main() {
    // working around issue #163
    // let none = None;

    // let some17 = Some(&17);
    // let some42 = Some(&42);
    // real tests
    let mut h1: MyHashMap<usize, isize> = MyHashMap::new(17);
    let mut h2: MyHashMap<usize, isize> = MyHashMap::new(42);
    let mut _x = h1.get(1);
    let mut _y = h1.get(2);
    let mut _z = h2.get(1);
    let mut _t = h2.get(2);
    // // assert!(x == none && y == none && z == none && t == none);
    // // proof_assert!(x == none && y == none && z == none && t == none);

    h1.add(1, 17);
    _x = h1.get(1);
    _y = h1.get(2);
    _z = h2.get(1);
    _t = h2.get(2);
    // // assert!(x == some17 && y == none && z == none && t == none);
    // // proof_assert!(x == some17 && y == none && z == none && t == none);
    h2.add(1, 42);
    _x = h1.get(1);
    _y = h1.get(2);
    _z = h2.get(1);
    _t = h2.get(2);
    // assert!(x == some17 && y == none && z == some42 && t == none);
    // proof_assert!(x == some17 && y == none && z == some42 && t == none);
}
