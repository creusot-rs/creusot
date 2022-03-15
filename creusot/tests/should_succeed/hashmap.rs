extern crate creusot_contracts;
use creusot_contracts::{std::vec, std::vec::Vec, std::Clone, *};

// to begin with, let's make hashmaps from u32 to i64 -> isize, not i64 see issue #311
// also, better idea to use 'usize' than 'u32' for indices

// #[derive(Clone)]
enum List {
    Nil,
    Cons(usize, isize, Box<List>),
}

impl Clone for List {
    #[trusted]
    fn clone(&self) -> Self {
        panic!()
        // std::clone::Clone::clone(self)
        //            <self as std::Clone>::clone()
    }
}

struct MyHashMap {
    buckets: Vec<List>,
}

#[predicate]
fn bucket_inv(l: List, index: Int, size: Int) -> bool {
    pearlite! {
        match l {
            List::Nil => true,
            List::Cons(k,_,tl) => @k % size === index && bucket_inv(*tl, index, size)
        }
    }
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
    std::process::abort()
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
        std::process::abort()
    }
}

impl MyHashMap {
    /* The data invariant of the HashMap structure
     */
    #[predicate]
    fn hashmap_inv(&self) -> bool {
        pearlite! {
            0 < (@(self.buckets)).len() &&
            forall<i: Int> 0 <= i && i < (@(self.buckets)).len() ==>
                bucket_inv((@(self.buckets))[i],i,(@(self.buckets)).len())
        }
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

    #[requires((*self).hashmap_inv())]
    #[ensures((^self).hashmap_inv())]
    #[ensures(forall<i:usize> (@^self).get(i) ===
              (if @i === @key { Some(val) } else { (@*self).get(i) } ))]
    fn add(&mut self, key: usize, val: isize) {
        let old_self = Ghost::record(&self);
        let length = self.buckets.len();
        proof_assert!(
          forall<i:Int> i >= 0 ==> 0 <= i % @length && i % @length < @length);
        let index: usize = key % length;
        let mut l: &mut List = &mut self.buckets[index];
        let old_l = Ghost::record(&l);
        #[invariant(prophecy_unchanged,^@old_self === ^self)]
        #[invariant(not_already_found,
                    get_in_bucket(*@old_l,@key) ===
                    get_in_bucket(*l,@key)
        )]
        #[invariant(magic_get_other, forall <i:Int>  ! (i === @key) ==>
                    get_in_bucket(^l,i) === get_in_bucket(*l,i) ==>
                    get_in_bucket(^@old_l,i) === get_in_bucket(*@old_l,i))]
        #[invariant(magic_get_key, get_in_bucket(^l,@key) === get_in_bucket(^@old_l,@key))]
        // #[invariant(natural_bucket_inv_others,
        //             forall <i:Int> 0 <= i && i < @length && ! (i === @index) ==>
        //                (@((^self).buckets))[i] === (@((*@old_self).buckets))[i]
        //             )]
        #[invariant(magic_bucket_inv_others,
                    forall <i:Int> 0 <= i && i < @length && ! (i === @index) ==>
                       (@((*self).buckets))[i] === (@((*@old_self).buckets))[i] ==>
                       (@((^self).buckets))[i] === (@((*@old_self).buckets))[i]
                    )]
        // #[invariant(natural_bucket_inv_index,
        //                bucket_inv(*@old_l,@index,@length)
        //             )]
        #[invariant(natural_bucket_inv_index,
                    bucket_inv(*l,@index,@length) ==>
                    bucket_inv((@((^self).buckets))[@index],@index,@length)
        )]
        #[invariant(bucket_inv_l,
                       bucket_inv(*l,@index,@length)
                    )]
        while let List::Cons(k, v, tl) = l {
            if *k == key {
                proof_assert!(bucket_inv(*l,@index,@length));
                *v = val;
                proof_assert!(bucket_inv(*l,@index,@length));
                proof_assert!(get_in_bucket(*l,@key) === Some(val));
                proof_assert!((@^self).get(key) === get_in_bucket(get_bucket(^self,@index),@key));
                proof_assert!(bucket_inv((@((^self).buckets))[@index],@index,@length));
                // the following is to simplify (case splitting) the proof of the post-condition
                proof_assert!(forall<i:usize>
                              if @i === @key {
                                  (@^self).get(i) === Some(val)
                              }
                              else {
                                  if @i % @length === @index {
                                      (@^self).get(i) === (@*self).get(i)
                                  }
                                  else {
                                      (@^self).get(i) === (@*self).get(i)
                                  }
                              });
                return;
            } else {
                l = &mut **tl;
            }
        }
          let l: List = std::mem::replace(&mut self.buckets[index], List::Nil);
          self.buckets[index] = List::Cons(key, val, Box::new(l));
          // the following is to simplify (case splitting) the proof of the post-condition
          proof_assert!(forall<i:usize>
                        if @i === @key {
                            (@^self).get(i) === Some(val)
                        }
                        else {
                            if @i % @length === @index {
                                (@^self).get(i) === (@*self).get(i)
                            }
                            else {
                                (@^self).get(i) === (@*self).get(i)
                            }
                        });
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
    // proof_assert!(
    //     forall<i:Int> 0 <= i && i < @size ==>
    //         get_bucket(res,i) === List::Nil);
    proof_assert!(
        forall<i:Int> i >= 0 ==> 0 <= i % @size && i % @size < @size);
    // proof_assert!(forall<i:Int> get_bucket(res,i % (@size)) === List::Nil);
    // proof_assert!(forall<i:Int> get_in_bucket(List::Nil,i) === None);
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
