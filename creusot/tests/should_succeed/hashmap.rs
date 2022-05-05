extern crate creusot_contracts;
use creusot_contracts::{std::vec, std::vec::Vec, std::Clone, *};

enum List {
    Nil,
    Cons(usize, isize, Box<List>),
}

impl Clone for List {
    #[trusted]
    #[ensures(result === *self)]
    fn clone(&self) -> Self {
        use List::*;
        match self {
            Nil => Nil,
            Cons(u, i, tl) => Cons(*u, *i, Box::new(Clone::clone(&*tl))),
        }
    }
}

struct MyHashMap {
    buckets: Vec<List>,
}

#[logic]
fn get_in_bucket(l: List, index: Int) -> Option<isize> {
    pearlite! {
        match l {
            List::Nil => None,
            List::Cons(k,v,tl) => if @k === index { Some(v) } else { get_in_bucket(*tl, index) }
        }
    }
}

#[logic]
#[trusted]
#[ensures(
    0 <= i && i < (@(h.buckets)).len() ==>
    result === (@(h.buckets))[i]
)]
fn get_bucket(h: MyHashMap, i: Int) -> List {
    absurd
}

impl Model for MyHashMap {
    type ModelTy = Mapping<usize, Option<isize>>;

    #[logic]
    #[trusted]
    #[ensures(
        forall<i:usize>
            result.get(i) === get_in_bucket(get_bucket(self,(@i) % (@(self.buckets)).len()),@i)
    )]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

impl MyHashMap {
    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<i:usize> (@^self).get(i) ===
              (if @i === @key { Some(val) } else { (@*self).get(i) } ))]
    fn add(&mut self, key: usize, val: isize) {
        use List::*;
        let old_self = Ghost::record(&self);
        let length = self.buckets.len();
        let index: usize = key % length;
        let mut l: &mut List = &mut self.buckets[index];
        let old_l = Ghost::record(&l);

        proof_assert! {
            forall<i : _, k : _> !(i === @key)  ==>
            get_in_bucket(get_bucket(*self, i), k) === get_in_bucket(get_bucket(*self, i), k)
        };

        #[invariant(y, ^@old_self === ^self)]
        #[invariant(z, (^self).hashmap_inv() ==> (^@old_self).hashmap_inv())]
        #[invariant(zz, get_in_bucket(^l, @key) === Some(val) ==> get_in_bucket(^@old_l, @key) === Some(val))]
        #[invariant(magic_get_other, forall <i:Int>
                     get_in_bucket(^l,i) === get_in_bucket(*l,i) ==>
                     get_in_bucket(^@old_l,i) === get_in_bucket(*@old_l,i))]
        while let Cons(k, v, tl) = l {
            if *k == key {
                *v = val;

                return;
            }

            l = &mut **tl;
        }

        creusot_contracts::std::mem::replace(l, Cons(key, val, Box::new(Nil)));
    }

    #[requires(self.hashmap_inv())]
    #[ensures(result === (@self).get(key))]
    fn get(&self, key: usize) -> Option<isize> {
        let index: usize = key % self.buckets.len();
        let mut l: &List = &self.buckets[index];
        #[invariant(not_already_found,
                    get_in_bucket(get_bucket(*self,@index),@key) ===
                    get_in_bucket(*l,@key)
        )]
        while let List::Cons(k, v, tl) = l {
            if *k == key {
                return Some(*v);
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

#[requires(0 < @size)]
#[ensures(result.hashmap_inv())]
#[ensures(forall<i:usize> (@result).get(i) === None)]
fn create(size: usize) -> MyHashMap {
    let res = MyHashMap {
        // buckets : vec![List::Nil;size]
        buckets: vec::from_elem(List::Nil, size),
    };
    proof_assert!(
        forall<i:Int> i >= 0 ==> 0 <= i % @size && i % @size < @size);
    res
}

fn main() {
    // working around issue #163
    let none = None;
    let some17 = Some(17);
    let some42 = Some(42);
    // real tests
    let mut h1: MyHashMap = create(17);
    let mut h2: MyHashMap = create(42);
    let mut x = h1.get(1);
    let mut y = h1.get(2);
    let mut z = h2.get(1);
    let mut t = h2.get(2);
    // assert!(x == none && y == none && z == none && t == none);
    proof_assert!(x === none && y === none && z === none && t === none);
    h1.add(1, 17);
    x = h1.get(1);
    y = h1.get(2);
    z = h2.get(1);
    t = h2.get(2);
    // assert!(x === some17 && y === none && z === none && t === none);
    proof_assert!(x === some17 && y === none && z === none && t === none);
    h2.add(1, 42);
    x = h1.get(1);
    y = h1.get(2);
    z = h2.get(1);
    t = h2.get(2);
    // assert!(x === some17 && y === none && z === some42 && t === none);
    proof_assert!(x === some17 && y === none && z === some42 && t === none);
}
