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

// Association lists
impl<K : Model, V> List<(K, V)> {
    #[predicate]
    fn mem(self, e: (K, V)) -> bool {
        pearlite! {
            match self {
                List::Cons((k, v), tl) => @e.0 === @k && e.1 === v || tl.mem(e),
                List::Nil => false,
            }
        }
    }

    // #[predicate]
    // fn contains(self, k: K) -> bool {
    //     pearlite! {
    //         match self {
    //             List::Cons((k2, _), tl) => @k === @k2 || tl.contains(k),
    //             List::Nil => false,
    //         }
    //     }
    // }
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
        #[invariant(l, (@(@old_self).buckets).len() === (@self.buckets).len())]
        #[invariant(xx, self.good_bucket(*l, @index ))]
        #[invariant(xx, self.good_bucket(^l, @index ) ==> self.good_bucket(^@old_l, @index ))]
        #[invariant(zzz, (@old_self).data_inv(*l) )]
        #[invariant(dumb, forall<i : _> 0 <= i  && ! (i === @index) && i < @length ==> self.data_inv((@self.buckets)[i]) && self.good_bucket((@self.buckets)[i], i))]
        #[invariant(data, (^self).data_inv(^l) ==> (^self).data_inv(^@old_l))]
        #[invariant(zz, get_in_bucket(^l, key) === Some(val) ==> get_in_bucket(^@old_l, key) === Some(val))]
        #[invariant(magic_get_other, forall <i:_>
                     get_in_bucket(^l,i) === get_in_bucket(*l,i) ==>
                     get_in_bucket(^@old_l,i) === get_in_bucket(*@old_l,i))]
        while let Cons((k, v), tl) = l {
            let tl = tl;
            if *k == key {
                *v = val;

                proof_assert! { (@old_self).data_inv(**tl)};

                // C'est cette ligne qu'il faut prouver
                proof_assert! { (self).data_inv(**tl) };

                proof_assert! { (self).data_inv(*l) };
                proof_assert! { (self).good_bucket(*l, @index) };
                proof_assert! { (self).hashmap_inv() };
                return;
            }
            l = &mut **tl;
        }

        *l = Cons((key, val), Box::new(Nil));
        proof_assert! { !((@self.buckets)[@index] === List::Nil)};
        proof_assert! { get_in_bucket(self.bucket(key), key) === Some(val) };
        proof_assert! { get_in_bucket(^@old_l, key) === Some(val) };
        proof_assert! { (@self).get(@key) === Some(val) };

        proof_assert! { forall<x :K , y: K>  @x === @y ==> x.hash_log() === y.hash_log() };
        proof_assert! { (self).data_inv(*l) };
        proof_assert! { (self).good_bucket(*l, @index) };
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

    // TODO: Cleanup.
    #[requires((@self.buckets).len() < 1000)]
    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<k : K> (@^self).get(@k) === (@*self).get(@k))] // lets prove the extensional version for now
    fn resize(&mut self) {
        let self_old = Ghost::record(&self);
        let mut new = Self::new(self.buckets.len() * 2);

        let mut i: usize = 0;
        #[invariant(x,
            forall<k : K> k.hash_log() % (@self.buckets).len() < @i ==>
                (@*@self_old).get(@k) === (@new).get(@k)
        )]
        #[invariant(x,
            forall<k : K> @i <= (@self_old).bucket_ix(k) && (@self_old).bucket_ix(k) <= (@(@self_old).buckets).len()  ==>
                (@new).get(@k) === None
        )]
        #[invariant(rest, forall<j : Int> @i <= j && j < (@(@self_old).buckets).len() ==> (@self.buckets)[j] === (@(@self_old).buckets)[j])]
        #[invariant(a, new.hashmap_inv())]
        #[invariant(p, ^@self_old === ^self)]
        #[invariant(l, (@(@self_old).buckets).len() === (@self.buckets).len())]
        #[invariant(z, @i <= (@self.buckets).len())]
        while i < self.buckets.len() {
            let mut l: List<_> =
                creusot_contracts::std::mem::replace(&mut self.buckets[i], List::Nil);
            let old_l = Ghost::record(&l);

            // proof_assert! { }
            // proof_assert! { good_hash(l, @i) };
            // this would be much simpler with ghost code
            #[invariant(a, new.hashmap_inv())]
            #[invariant(x,
            forall<k : K> k.hash_log() % (@self.buckets).len() < @i ==>
                (@*@self_old).get(@k) === (@new).get(@k)
            )]
            #[invariant(x,
                forall<k : K> @i < (@self_old).bucket_ix(k) && (@self_old).bucket_ix(k) <= (@(@self_old).buckets).len()  ==>
                    (@new).get(@k) === None
            )]
            // Need bijection
            // #[invariant(added, forall<k : K, v: _> k.hash_log() % (@self.buckets).len() === @i ==>
            //     get_in_bucket(@old_l, k) === Some(v) ==> (@new).get(@k) === Some(v) || get_in_bucket(l, k) === Some(v)
            // )]
            // #[invariant(other, forall<k : K, v: _> k.hash_log() % (@self.buckets).len() === @i ==>
            //     (@new).get(@k) === Some(v) ==> get_in_bucket(@old_l, k) === Some(v)
            // )]
            #[invariant(zzz1, forall<k : K, v : V> (@self_old).bucket_ix(k) === @i ==> get_in_bucket(@old_l, k) === Some(v) ==> (@new).get(@k) === Some(v) || get_in_bucket(l, k) === Some(v))]
            #[invariant(zzz2, forall<k : K, v : V> (@self_old).bucket_ix(k) === @i ==> ( (@new).get(@k) === Some(v)) ==> get_in_bucket(@old_l, k) === Some(v))]
            #[invariant(d, (@self_old).data_inv(l))]
            #[invariant(x, (@self_old).good_bucket(l, @i))]
            while let List::Cons(e, tl) = l {
                let (k, v) = e;
                new.add(k, v);
                l = *tl;
            }
            proof_assert! { forall<k : K, v : V>
                (@self_old).bucket_ix(k) === @i ==> get_in_bucket(@old_l, k) === (@*@self_old).get(@k)
            }

            proof_assert! { forall<k : K, v : V> (@self_old).bucket_ix(k) === @i ==> (@old_l).mem((k, v)) ==> (@new).get(@k) === Some(v) };
            // proof_assert! { forall<k : K, v : V> (@self_old).bucket_ix(k) === @i ==> ((@new).get(@k) === Some(v)) ==> (@old_l).mem((k, v)) };
            proof_assert! { @old_l === (@((@self_old).buckets))[@i]};
            proof_assert! { forall<k : K, v : V> (@self_old).bucket_ix(k) === @i ==> (@*@self_old).get(@k) === Some(v) ==> (@new).get(@k) === Some(v) };

            proof_assert! { forall<k : K> (@self_old).bucket_ix(k) === @i  ==>
                (@*@self_old).get(@k) === (@new).get(@k)
            };
            i += 1;
        }

        proof_assert! { @i === (@self.buckets).len() };
        proof_assert! { forall<k : K> (@*@self_old).get(@k) === (@new).get(@k)};
        *self = new;
    }

    #[predicate]
    fn data_inv(self, l : List<(K, V)>) -> bool {
        pearlite! {
            forall<k : _, v: _> (l.mem((k, v)) ==> (@self).get(@k) === Some(v))
        }
    }

    #[predicate]
    fn good_bucket(self, l: List<(K, V)>, h: Int) -> bool {
        pearlite! {
            forall<k : _, v: _> l.mem((k, v)) ==> self.bucket_ix(k) === h
        }
    }

    /* The data invariant of the HashMap structure
     */
    #[predicate]
    fn hashmap_inv(&self) -> bool {
        pearlite! {
            0 < (@(self.buckets)).len() &&
            forall<i : _> 0 <= i && i < (@self.buckets).len() ==> self.data_inv((@self.buckets)[i]) && self.good_bucket((@self.buckets)[i], i)
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
