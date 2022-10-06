extern crate creusot_contracts;
use creusot_contracts::{
    logic::{Int, Mapping},
    *,
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
    fn get(self, index: K::DeepModelTy) -> Option<V> {
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

// A slightly simplified version of the Rust hashing mechanisms, this sufficiently captures the behavior though
trait Hash: DeepModel {
    #[ensures(@result == Self::hash_log(self.deep_model()))]
    fn hash(&self) -> u64;

    #[logic]
    fn hash_log(_: Self::DeepModelTy) -> Int;
}

impl Hash for usize {
    #[ensures(@result == Self::hash_log(self.deep_model()))]
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

impl<K: Hash, V> ShallowModel for MyHashMap<K, V> {
    type ShallowModelTy = Mapping<K::DeepModelTy, Option<V>>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { |k| self.bucket(k).get(k) }
    }
}
impl<K: Hash, V> MyHashMap<K, V> {
    #[logic]
    fn bucket(self, k: K::DeepModelTy) -> List<(K, V)> {
        pearlite! { (@self.buckets)[self.bucket_ix(k)] }
    }

    #[logic]
    fn bucket_ix(self, k: K::DeepModelTy) -> Int {
        pearlite! { K::hash_log(k).rem_euclid((@self.buckets).len()) }
    }
}

impl<K: Hash + Copy + Eq + DeepModel, V: Copy> MyHashMap<K, V> {
    #[requires(0 < @size)]
    #[ensures(result.hashmap_inv())]
    #[ensures(forall<i: K::DeepModelTy> (@result).get(i) == None)]
    pub fn new(size: usize) -> MyHashMap<K, V> {
        let res = MyHashMap { buckets: vec![List::Nil; size] };
        res
    }

    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<i: K::DeepModelTy> (@^self).get(i) == (if i == key.deep_model() { Some(val) } else { (@self).get(i) } ))]
    pub fn add(&mut self, key: K, val: V) {
        use List::*;
        let old_self = ghost! { self };
        let length = self.buckets.len();
        let index: usize = key.hash() as usize % length;
        let mut l: &mut List<_> = &mut self.buckets[index];
        let old_l = ghost! { l };

        #[invariant(y, ^old_self.inner() == ^self)]
        #[invariant(xx, self.good_bucket(*l, @index))]
        #[invariant(xx, self.good_bucket(^l, @index) ==> self.good_bucket(^old_l.inner(), @index ))]
        #[invariant(get_key, (^l).get(key.deep_model()) == Some(val) ==> (^*old_l).get(key.deep_model()) == Some(val))]
        #[invariant(get_rest, forall <i:_> (^l).get(i) == (*l).get(i) ==> (^*old_l).get(i) == old_l.get(i))]
        #[invariant(no_double_binding, (*l).no_double_binding())]
        #[invariant(no_double_binding_magic, (forall <i:_> (*l).get(i) == (^l).get(i) || i == key.deep_model()) && (^l).no_double_binding() ==>
                                             (^*old_l).no_double_binding())]
        while let Cons((k, v), tl) = l {
            let tl = tl;
            if *k == key {
                *v = val;
                proof_assert! { (self).hashmap_inv() };
                return;
            }
            l = &mut **tl;
        }

        *l = Cons((key, val), Box::new(Nil));

        proof_assert! { (self).hashmap_inv() };
    }

    #[requires(self.hashmap_inv())]
    #[ensures(match result {
        Some(v) => (@self).get(key.deep_model()) == Some(*v),
        None => (@self).get(key.deep_model()) == None,
    })]
    pub fn get(&self, key: K) -> Option<&V> {
        let index: usize = key.hash() as usize % self.buckets.len();
        let mut l = &self.buckets[index];

        #[invariant(not_already_found, self.bucket(key.deep_model()).get(key.deep_model()) == (*l).get(key.deep_model()))]
        while let List::Cons((k, v), tl) = l {
            if *k == key {
                return Some(v);
            }
            l = &**tl;
        }
        return None;
    }

    // TODO: Cleanup.
    #[requires((@self.buckets).len() < 1000)]
    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<k : K::DeepModelTy> (@^self).get(k) == (@self).get(k))] // lets prove the extensional version for now
    #[allow(dead_code)]
    fn resize(&mut self) {
        let old_self = ghost! { self };
        let mut new = Self::new(self.buckets.len() * 2);

        let mut i: usize = 0;
        #[invariant(seen, forall<k : K::DeepModelTy> old_self.bucket_ix(k) < @i ==> (@old_self).get(k) == (@new).get(k))]
        #[invariant(unseen, forall<k : K::DeepModelTy>
            @i <=   old_self.bucket_ix(k) &&
                    old_self.bucket_ix(k) <= (@old_self.buckets).len() ==> (@new).get(k) == None
        )]
        #[invariant(rest, forall<j : Int> @i <= j && j < (@old_self.buckets).len() ==> (@self.buckets)[j] == (@old_self.buckets)[j])]
        #[invariant(a, new.hashmap_inv())]
        #[invariant(p, ^old_self.inner() == ^self)]
        #[invariant(l, (@old_self.buckets).len() == (@self.buckets).len())]
        #[invariant(z, @i <= (@self.buckets).len())]
        while i < self.buckets.len() {
            let mut l: List<_> = std::mem::replace(&mut self.buckets[i], List::Nil);

            #[invariant(a, new.hashmap_inv())]
            #[invariant(x, forall<k : K::DeepModelTy> old_self.bucket_ix(k) < @i ==> (@old_self).get(k) == (@new).get(k))]
            #[invariant(x, forall<k : K::DeepModelTy>
                @i < old_self.bucket_ix(k) && old_self.bucket_ix(k) <= (@old_self.buckets).len()  ==> (@new).get(k) == None
            )]
            #[invariant(zzz, forall<k : K::DeepModelTy> old_self.bucket_ix(k) == @i ==>
                        (@old_self).get(k) == match l.get(k) { None => (@new).get(k), Some(v) => Some(v) })]
            #[invariant(l_no_double_binding, l.no_double_binding())]
            #[invariant(x, old_self.good_bucket(l, @i))]
            while let List::Cons((k, v), tl) = l {
                new.add(k, v);
                l = *tl;
            }
            proof_assert! { forall<k : K::DeepModelTy> old_self.bucket_ix(k) == @i  ==> (@old_self).get(k) == (@new).get(k) };
            i += 1;
        }

        *self = new;
    }

    #[predicate]
    fn good_bucket(self, l: List<(K, V)>, h: Int) -> bool {
        pearlite! {
            forall<k : K::DeepModelTy, v: _> l.get(k) == Some(v) ==> self.bucket_ix(k) == h
        }
    }

    /* The data invariant of the HashMap structure
     */
    #[predicate]
    fn hashmap_inv(&self) -> bool {
        pearlite! {
            0 < (@self.buckets).len() &&
            forall<i : _> 0 <= i && i < (@self.buckets).len() ==> self.good_bucket((@self.buckets)[i], i) && (@self.buckets)[i].no_double_binding()
        }
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
