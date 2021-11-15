
// The following code is the Sparse Arrays Verification Challenge from
// the VACID0 benchmark
//
// K. Rustan M. Leino and Michał Moskal. VACID-0: Verification of
// ample correctness of invariants of data-structures, edition 0. In
// Proceedings of Tools and Experiments Workshop at VSTTE, 2010.
//
// A first challenge is to handle enough separation information so
// that the test Harness involving two disjoint sparse arrays can be
// proved. A second challenge is the assertion in the code of add() to
// show that the array is not accessed outside its bound: the proof
// requires to reason about permutation,


extern crate creusot_contracts;
//use crate::{std::clone::Clone, Int, Model, Seq};
use creusot_contracts::{std::vec, std::vec::Vec, *};

#[predicate]
fn interval(a:Int, x:Int, b:Int) -> bool {
    a <= x && x < b
}



struct Sparse<T> {
    size: usize,        // allocated size
    n: usize,           // number of elements stored so far
    values: Vec<T>,     // actual values at their actual indexes
    idx: Vec<usize>,    // corresponding indexes in back
    back: Vec<usize>,   // corresponding indexes in idx, makes sense between 0 and n-1
}


impl<T> Model for Sparse<T> {
    type ModelTy = Seq<Option<T>>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}



#[predicate]
fn sparse_inv<T>(x: Sparse<T>) -> bool {
    pearlite! {
        interval(0,@(x.n),@(x.size))
            && @(x.values).len() === @(x.size)
            && @(x.idx).len() === @(x.size)
            && @(x.back).len() === @(x.size)
            && forall<i: Int> interval(0,i,@(x.n)) ==>
            match Seq::get(@(x.back),i) {
                None => false,
                Some(j) => interval(0,@j,@(x.size))
                    && match Seq::get(@(x.idx),@j) {
                        None => false,
                        Some(k) => @k === i,
                    }
            }
    }
}





/* is_elt(a,i) tells whether index i points to a existing element. It
  can be checked as follows:

  (1) check that array idx maps i to a index j between 0 and n (excluded)
  (2) check that back(j) is i
*/

// predicate is_elt(a: Sparse (alpha) [R], i: int) =
//   [0] <= [select (!(!a.idx).cell, i)]
//   and [select (!(!a.idx).cell, i)] < [!a.n]
//   and [select (!(!a.back).cell, select (!(!a.idx).cell, i))] = [i]



// logic function model (Sparse (alpha) [R], int): alpha

// axiom model_in:
//   forall a: Sparse (alpha) [R].
//   forall i: int.
//   is_elt([a], [i]) ==> [model(a, i)] = [select(!(!a.value).cell, i)]

// axiom model_out:
//   forall a: Sparse (alpha) [R].
//   forall i: int.
//   not is_elt([a], [i]) ==> [model(a, i)] = [!a.default]




#[requires(0 <= @sz)]
#[ensures( (@result).len() === @sz)]
#[ensures(forall<i: Int> (@result)[i] === None)]
fn create<T:Clone+Copy>(sz:usize, dummy: T) -> Sparse<T> {
    Sparse {
        size : sz,
        n : 0,
        // values : vec![dummy;sz],
        values : vec::from_elem(dummy,sz),
        // idx : vec![0;sz],
        idx : vec::from_elem(0,sz),
        // back : vec![0;sz],
        back : vec::from_elem(0,sz),
    }
}


impl <T> Sparse<T> {

    #[requires(interval(0,@i,(@self).len()))]
    // #[ensures(result === (@self)[@i])]
    fn get(&self, i: usize) -> Option<&T> {
        let index = self.idx[i];
        if index < self.n && self.back[index] == i {
            Some(&self.values[i])
        }
        else {
            None
        }
    }


   // use map.MapInjection as MI

   // lemma permutation :
   //   forall a: sparse_array 'a.
   //    sparse_inv(a) ->
   //    a.card = a.length ->
   //    forall i: int. 0 <= i < a.length -> is_elt a i
   //      by MI.surjective a.back.elts a.card
   //      so exists j. 0 <= j < a.card /\ a.back[j] = i


    #[requires(interval(0,@i,(@*self).len()))]
    #[ensures( (@^self).len() === (@*self).len())]
    #[ensures(forall<j: Int> !(j === @i) ==> (@^self)[j] === (@*self)[j])]
    #[ensures((@^self)[@i] === Some(v))]
    fn set(&mut self, i: usize, v: T) {
        self.values[i] = v;
        let index = self.idx[i];
        if !(index < self.n && self.back[index] == i) {
            // the hard assertion!
            assert!(self.n < self.size);
            self.idx[i] = self.n;
            self.back[self.n] = i;
            self.n += 1;
        }
    }

}


fn main () {
    let default = 0;
    let mut a = create(10,default);
    let mut b = create(20,default);
    let x = a.get(5);
    let y = b.get(7);
    proof_assert!(x === None && y === None);
    // assert!(x == None && y == None);
    a.set(5, 1);
    b.set(7, 2);
    let x = a.get(5);
    let y = b.get(7);
    // proof_assert!(match x {
    //     None => false,
    //     Some(z) => z === 1
    // });
    // proof_assert!(match y {
    //     None => false,
    //     Some(z) => z === 2
    // });
    // assert!(x == Some(1) && y == Some(2));
    let x = a.get(7);
    let y = b.get(5);
    proof_assert!(x === None && y === None);
    // assert!(x == None && y == None);
    let x = a.get(0);
    let y = b.get(0);
    proof_assert!(x === None && y === None);
    // assert!(x == None && y == None);
    let x = a.get(9);
    let y = b.get(9);
    proof_assert!(x === None && y === None)
    // assert!(x == None && y == None);
}
