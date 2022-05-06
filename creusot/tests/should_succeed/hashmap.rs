extern crate creusot_contracts;
use creusot_contracts::{std::vec, std::vec::Vec, std::Clone, *};

extern_spec! {
    #[ensures(result === (@self_ === @rhs))]
    fn std::cmp::PartialEq::eq<T, Rhs>(self_: &T, rhs: &Rhs) -> bool
        where T : PartialEq<Rhs>,
              T : Model,
              Rhs: Model<ModelTy = T::ModelTy>,
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

// A slightly simplified version of the Rust hashing mechanisms, this sufficiently captures the behavior though
trait Hash {
    #[ensures(@result === self.hash_log())]
    fn hash(&self) -> u64;

    #[logic]
    #[ensures(result >= 0)]
    fn hash_log(self) -> Int;
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
}

struct MyHashMap<K, V> {
    buckets: Vec<List<(K, V)>>,
}

#[logic]
fn get_in_bucket<K: Model, V>(l: List<(K, V)>, index: K) -> Option<V> {
    pearlite! {
        match l {
            List::Nil => None,
            List::Cons((k,v),tl) => if @k === @index { Some(v) } else { get_in_bucket(*tl, index) }
        }
    }
}

impl<K: Hash + Model, V> Model for MyHashMap<K, V> {
    type ModelTy = Mapping<K::ModelTy, Option<V>>;

    #[logic]
    #[trusted]
    #[ensures(
        forall<k : _>
            result.get(@k) === get_in_bucket(self.bucket(k),k)
    )]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}
impl<K: Hash, V> MyHashMap<K, V> {
    #[logic]
    #[trusted]
    #[ensures(
        result === (@(self.buckets))[k.hash_log() % (@self.buckets).len()]
    )]
    fn bucket(self, k: K) -> List<(K, V)> {
        absurd
    }
}

impl<K: Hash + Copy + Eq + Model, V: Copy> MyHashMap<K, V> {
    #[requires(0 < @size)]
    #[ensures(result.hashmap_inv())]
    #[ensures(forall<i: K> (@result).get(@i) === None)]
    fn new(size: usize) -> MyHashMap<K, V> {
        let res = MyHashMap { buckets: vec::from_elem(List::Nil, size) };

        proof_assert!(forall<k : K> k.hash_log() % (@res.buckets).len() >= 0 && k.hash_log() % (@res.buckets).len() < (@res.buckets).len());
        proof_assert! { forall<k : _> res.bucket(k) === List::Nil };

        res
    }

    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<i: K> (@^self).get(@i) ===
              (if @i === @key { Some(val) } else { (@*self).get(@i) } ))]
    fn add(&mut self, key: K, val: V) {
        use List::*;
        let old_self = Ghost::record(&self);
        let length = self.buckets.len();
        let index: usize = key.hash() as usize % length;
        let mut l: &mut List<_> = &mut self.buckets[index];
        let old_l = Ghost::record(&l);

        #[invariant(y, ^@old_self === ^self)]
        #[invariant(z, (^self).hashmap_inv() ==> (^@old_self).hashmap_inv())]
        #[invariant(zz, get_in_bucket(^l, key) === Some(val) ==> get_in_bucket(^@old_l, key) === Some(val))]
        #[invariant(magic_get_other, forall <i:_>
                     get_in_bucket(^l,i) === get_in_bucket(*l,i) ==>
                     get_in_bucket(^@old_l,i) === get_in_bucket(*@old_l,i))]
        while let Cons((k, v), tl) = l {
            if *k == key {
                *v = val;
                return;
            }
            l = &mut **tl;
        }

        creusot_contracts::std::mem::replace(l, Cons((key, val), Box::new(Nil)));
    }

    #[requires(self.hashmap_inv())]
    #[ensures(match result {
        Some(v) => (@self).get(@key) === Some(*v),
        None => (@self).get(@key) === None,
    })]
    fn get(&self, key: K) -> Option<&V> {
        let index: usize = key.hash() as usize % self.buckets.len();
        let mut l = &self.buckets[index];

        proof_assert! { self.bucket(key) === *l };
        #[invariant(not_already_found,
                    get_in_bucket(self.bucket(key), key) ===
                    get_in_bucket(*l, key)
        )]
        while let List::Cons((k, v), tl) = l {
            if *k == key {
                return Some(v);
            }
            l = &**tl;
        }
        return None;
    }

    /* The data invariant of the HashMap structure
     */
    #[predicate]
    fn hashmap_inv(&self) -> bool {
        pearlite! {
            0 < (@(self.buckets)).len()
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
