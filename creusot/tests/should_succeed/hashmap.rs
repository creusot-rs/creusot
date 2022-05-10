extern crate creusot_contracts;
use creusot_contracts::{std::vec, *};

extern_spec! {
    #[ensures(result === (@self_ === @rhs))]
    fn std::cmp::PartialEq::eq<Self_, Rhs>(self_: &Self_, rhs: &Rhs) -> bool
        where Self_ : PartialEq<Rhs>,
              Self_ : Model,
              Rhs: Model<ModelTy = Self_::ModelTy>,
}

enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T: Clone> Clone for List<T> {
    #[trusted]
    #[ensures(result === *self)]
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
                List::Cons((k,v),tl) => if @k === index { Some(v) } else { tl.get(index) }
            }
        }
    }

    #[predicate]
    fn no_double_binding(self) -> bool {
        pearlite! {
            match self {
                List::Nil => true,
                List::Cons((k, v), tl) => tl.get(@k) === None && tl.no_double_binding()
            }
        }
    }
}

// A slightly simplified version of the Rust hashing mechanisms, this sufficiently captures the behavior though
trait Hash: Model {
    #[ensures(@result === self.hash_log())]
    fn hash(&self) -> u64;

    #[logic]
    #[ensures(result >= 0)]
    fn hash_log(self) -> Int;

    #[law]
    #[requires(@x === @y)]
    #[ensures(x.hash_log() === y.hash_log())]
    fn hash_log_eq_model(x: Self, y: Self);
}

impl Hash for usize {
    #[ensures(@result === self.hash_log())]
    fn hash(&self) -> u64 {
        *self as u64
    }

    #[logic]
    fn hash_log(self) -> Int {
        pearlite! { @self }
    }

    #[logic]
    #[requires(@x === @y)]
    #[ensures(x.hash_log() === y.hash_log())]
    fn hash_log_eq_model(x: Self, y: Self) {}
}

struct MyHashMap<K, V> {
    buckets: Vec<List<(K, V)>>,
}

impl<K: Hash + Model, V> Model for MyHashMap<K, V> {
    type ModelTy = Mapping<K::ModelTy, Option<V>>;

    #[logic]
    #[trusted]
    #[ensures(forall<k : _> result.get(@k) === self.bucket(k).get(@k))]
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
    #[ensures(forall<i: K> (@result).get(@i) === None)]
    fn new(size: usize) -> MyHashMap<K, V> {
        let res = MyHashMap { buckets: vec::from_elem(List::Nil, size) };
        res
    }

    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<i: K> (@^self).get(@i) === (if @i === @key { Some(val) } else { (@*self).get(@i) } ))]
    fn add(&mut self, key: K, val: V) {
        use List::*;
        let old_self = Ghost::record(&self);
        let length = self.buckets.len();
        let index: usize = key.hash() as usize % length;
        let mut l: &mut List<_> = &mut self.buckets[index];
        let old_l = Ghost::record(&l);

        #[invariant(y, ^@old_self === ^self)]
        #[invariant(xx, self.good_bucket(*l, @index))]
        #[invariant(xx, self.good_bucket(^l, @index) ==> self.good_bucket(^@old_l, @index ))]
        #[invariant(get_key, (^l).get(@key) === Some(val) ==> (^@old_l).get(@key) === Some(val))]
        #[invariant(get_rest, forall <i:_> (^l).get(i) === (*l).get(i) ==> (^@old_l).get(i) === (*@old_l).get(i))]
        #[invariant(no_double_binding, (*l).no_double_binding())]
        #[invariant(no_double_binding_magic, (forall <i:_> (*l).get(i) === (^l).get(i) || i === @key) && (^l).no_double_binding() ==> (^@old_l).no_double_binding())]
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
        Some(v) => (@self).get(@key) === Some(*v),
        None => (@self).get(@key) === None,
    })]
    fn get(&self, key: K) -> Option<&V> {
        let index: usize = key.hash() as usize % self.buckets.len();
        let mut l = &self.buckets[index];

        #[invariant(not_already_found, self.bucket(key).get(@key) === (*l).get(@key))]
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
    #[ensures(forall<k : K> (@^self).get(@k) === (@*self).get(@k))] // lets prove the extensional version for now
    fn resize(&mut self) {
        let self_old = Ghost::record(&self);
        let mut new = Self::new(self.buckets.len() * 2);

        let mut i: usize = 0;
        #[invariant(seen, forall<k : K> (@self_old).bucket_ix(k) < @i ==> (@*@self_old).get(@k) === (@new).get(@k))]
        #[invariant(unseen, forall<k : K>
            @i <=   (@self_old).bucket_ix(k) &&
                    (@self_old).bucket_ix(k) <= (@(@self_old).buckets).len() ==> (@new).get(@k) === None
        )]
        #[invariant(rest, forall<j : Int> @i <= j && j < (@(@self_old).buckets).len() ==> (@self.buckets)[j] === (@(@self_old).buckets)[j])]
        #[invariant(a, new.hashmap_inv())]
        #[invariant(p, ^@self_old === ^self)]
        #[invariant(l, (@(@self_old).buckets).len() === (@self.buckets).len())]
        #[invariant(z, @i <= (@self.buckets).len())]
        while i < self.buckets.len() {
            let mut l: List<_> =
                creusot_contracts::std::mem::replace(&mut self.buckets[i], List::Nil);

            #[invariant(a, new.hashmap_inv())]
            #[invariant(x, forall<k : K> (@self_old).bucket_ix(k) < @i ==> (@*@self_old).get(@k) === (@new).get(@k))]
            #[invariant(x, forall<k : K>
                @i < (@self_old).bucket_ix(k) && (@self_old).bucket_ix(k) <= (@(@self_old).buckets).len()  ==> (@new).get(@k) === None
            )]
            #[invariant(zzz, forall<k : K> (@self_old).bucket_ix(k) === @i ==>
                        (@@self_old).get(@k) === match l.get(@k) { None => (@new).get(@k), Some(v) => Some(v) })]
            #[invariant(l_no_double_binding, l.no_double_binding())]
            #[invariant(x, (@self_old).good_bucket(l, @i))]
            while let List::Cons((k, v), tl) = l {
                new.add(k, v);
                l = *tl;
            }
            proof_assert! { forall<k : K, v: V> (@self_old).bucket_ix(k) === @i  ==> (@*@self_old).get(@k) === (@new).get(@k) };
            i += 1;
        }

        *self = new;
    }

    #[predicate]
    fn good_bucket(self, l: List<(K, V)>, h: Int) -> bool {
        pearlite! {
            forall<k : _, v: _> l.get(@k) === Some(v) ==> self.bucket_ix(k) === h
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

fn main() {
    // working around issue #163
    // let none = None;

    // let some17 = Some(&17);
    // let some42 = Some(&42);
    // real tests
    let mut h1: MyHashMap<usize, isize> = MyHashMap::new(17);
    let mut h2: MyHashMap<usize, isize> = MyHashMap::new(42);
    let mut x = h1.get(1);
    let mut y = h1.get(2);
    let mut z = h2.get(1);
    let mut t = h2.get(2);
    // // assert!(x == none && y == none && z == none && t == none);
    // // proof_assert!(x === none && y === none && z === none && t === none);

    h1.add(1, 17);
    x = h1.get(1);
    y = h1.get(2);
    z = h2.get(1);
    t = h2.get(2);
    // // assert!(x === some17 && y === none && z === none && t === none);
    // // proof_assert!(x === some17 && y === none && z === none && t === none);
    h2.add(1, 42);
    x = h1.get(1);
    y = h1.get(2);
    z = h2.get(1);
    t = h2.get(2);
    // assert!(x === some17 && y === none && z === some42 && t === none);
    // proof_assert!(x === some17 && y === none && z === some42 && t === none);
}
