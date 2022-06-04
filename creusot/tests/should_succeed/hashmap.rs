// UNSTABLE

extern crate creusot_contracts;
use creusot_contracts::{std::vec, *};

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

impl<K: Model, V> List<(K, V)> {
    #[logic]
    fn get(self, index: K::ModelTy) -> Option<V> {
        pearlite! {
            match self {
                List::Nil => None,
                List::Cons((k,v),tl) => if @k == index { Some(v) } else { tl.get(index) }
            }
        }
    }

    #[predicate]
    fn no_double_binding(self) -> bool {
        pearlite! {
            match self {
                List::Nil => true,
                List::Cons((k, _), tl) => tl.get(@k) == None && tl.no_double_binding()
            }
        }
    }
}

// A slightly simplified version of the Rust hashing mechanisms, this sufficiently captures the behavior though
trait Hash: Model {
    #[ensures(@result == self.hash_log())]
    fn hash(&self) -> u64;

    #[logic]
    #[ensures(result >= 0)]
    fn hash_log(self) -> Int;

    #[law]
    #[requires(@x == @y)]
    #[ensures(x.hash_log() == y.hash_log())]
    fn hash_log_eq_model(x: Self, y: Self);
}

impl Hash for usize {
    #[ensures(@result == self.hash_log())]
    fn hash(&self) -> u64 {
        *self as u64
    }

    #[logic]
    #[ensures(result >= 0)]
    fn hash_log(self) -> Int {
        pearlite! { @self }
    }

    #[logic]
    #[requires(@x == @y)]
    #[ensures(x.hash_log() == y.hash_log())]
    fn hash_log_eq_model(x: Self, y: Self) {}
}

struct MyHashMap<K, V> {
    buckets: Vec<List<(K, V)>>,
}

impl<K: Hash + Model, V> Model for MyHashMap<K, V> {
    type ModelTy = Mapping<K::ModelTy, Option<V>>;

    #[logic]
    #[trusted]
    #[ensures(forall<k : K> result.get(@k) == self.bucket(k).get(@k))]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}
impl<K: Hash, V> MyHashMap<K, V> {
    #[logic]
    fn bucket(self, k: K) -> List<(K, V)> {
        pearlite! { (@(self.buckets))[self.bucket_ix(k)] }
    }

    #[logic]
    fn bucket_ix(self, k: K) -> Int {
        pearlite! { k.hash_log() % (@self.buckets).len() }
    }
}

impl<K: Hash + Copy + Eq + Model, V: Copy> MyHashMap<K, V> {
    #[requires(0 < @size)]
    #[ensures(result.hashmap_inv())]
    #[ensures(forall<i: K> (@result).get(@i) == None)]
    pub fn new(size: usize) -> MyHashMap<K, V> {
        let res = MyHashMap { buckets: vec::from_elem(List::Nil, size) };
        res
    }

    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<i: K> (@^self).get(@i) == (if @i == @key { Some(val) } else { (@*self).get(@i) } ))]
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
        #[invariant(get_key, (^l).get(@key) == Some(val) ==> (^*old_l).get(@key) == Some(val))]
        #[invariant(get_rest, forall <i:_> (^l).get(i) == (*l).get(i) ==> (^*old_l).get(i) == old_l.get(i))]
        #[invariant(no_double_binding, (*l).no_double_binding())]
        #[invariant(no_double_binding_magic, (forall <i:_> (*l).get(i) == (^l).get(i) || i == @key) && (^l).no_double_binding() ==>
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
        Some(v) => (@self).get(@key) == Some(*v),
        None => (@self).get(@key) == None,
    })]
    pub fn get(&self, key: K) -> Option<&V> {
        let index: usize = key.hash() as usize % self.buckets.len();
        let mut l = &self.buckets[index];

        #[invariant(not_already_found, self.bucket(key).get(@key) == (*l).get(@key))]
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
    #[ensures(forall<k : K> (@^self).get(@k) == (@*self).get(@k))] // lets prove the extensional version for now
    #[allow(dead_code)]
    fn resize(&mut self) {
        let old_self = ghost! { self };
        let mut new = Self::new(self.buckets.len() * 2);

        let mut i: usize = 0;
        #[invariant(seen, forall<k : K> old_self.bucket_ix(k) < @i ==> (@*old_self).get(@k) == (@new).get(@k))]
        #[invariant(unseen, forall<k : K>
            @i <=   old_self.bucket_ix(k) &&
                    old_self.bucket_ix(k) <= (@old_self.buckets).len() ==> (@new).get(@k) == None
        )]
        #[invariant(rest, forall<j : Int> @i <= j && j < (@old_self.buckets).len() ==> (@self.buckets)[j] == (@old_self.buckets)[j])]
        #[invariant(a, new.hashmap_inv())]
        #[invariant(p, ^old_self.inner() == ^self)]
        #[invariant(l, (@old_self.buckets).len() == (@self.buckets).len())]
        #[invariant(z, @i <= (@self.buckets).len())]
        while i < self.buckets.len() {
            let mut l: List<_> = std::mem::replace(&mut self.buckets[i], List::Nil);

            #[invariant(a, new.hashmap_inv())]
            #[invariant(x, forall<k : K> (old_self).bucket_ix(k) < @i ==> (@*old_self).get(@k) == (@new).get(@k))]
            #[invariant(x, forall<k : K>
                @i < old_self.bucket_ix(k) && (old_self).bucket_ix(k) <= (@old_self.buckets).len()  ==> (@new).get(@k) == None
            )]
            #[invariant(zzz, forall<k : K> (old_self).bucket_ix(k) == @i ==>
                        (@old_self.inner()).get(@k) == match l.get(@k) { None => (@new).get(@k), Some(v) => Some(v) })]
            #[invariant(l_no_double_binding, l.no_double_binding())]
            #[invariant(x, old_self.good_bucket(l, @i))]
            while let List::Cons((k, v), tl) = l {
                new.add(k, v);
                l = *tl;
            }
            proof_assert! { forall<k : K> old_self.bucket_ix(k) == @i  ==> (@*old_self).get(@k) == (@new).get(@k) };
            i += 1;
        }

        *self = new;
    }

    #[predicate]
    fn good_bucket(self, l: List<(K, V)>, h: Int) -> bool {
        pearlite! {
            forall<k : K, v: _> l.get(@k) == Some(v) ==> self.bucket_ix(k) == h
        }
    }

    /* The data invariant of the HashMap structure
     */
    #[predicate]
    fn hashmap_inv(&self) -> bool {
        pearlite! {
            0 < (@(self.buckets)).len() &&
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
