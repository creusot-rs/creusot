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
use creusot_contracts::{std::vec, std::vec::Vec, *};

/* The sparse array data structure
 */
struct Sparse<T> {
    size: usize,      // allocated size
    n: usize,         // number of elements stored so far
    values: Vec<T>,   // actual values at their actual indexes
    idx: Vec<usize>,  // corresponding indexes in `back`
    back: Vec<usize>, // corresponding indexes in `idx`, makes sense between 0 and `n`-1
}

/* The function `s.is_elt(i)` tells whether index `i` points to a
 * existing element. It can be checked as follows:
 *   (1) check that array `idx` maps `i` to a index `j` between 0 and `n` (excluded)
 *   (2) check that `back[j]` is `i`
 */
impl<T> Sparse<T> {
    #[predicate]
    fn is_elt(&self, i: Int) -> bool {
        pearlite! { 0 <= i && i < @(self.size)
                    && @((@(self.idx))[i]) < @(self.n)
                    && @((@(self.back))[@((@(self.idx))[i])]) === i
        }
    }
}

/* The model of the structure is a sequence of optional values
 */
impl<T> Model for Sparse<T> {
    type ModelTy = Seq<Option<T>>;

    #[logic]
    #[trusted]
    #[ensures(result.len() === @(self.size))]
    #[ensures(
        forall<i:Int>
            result[i] ===
            (if self.is_elt(i) { Some((@(self.values))[i]) } else { None})
    )]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

/* The data invariant of the Sparse Array structure
 */
#[predicate]
fn sparse_inv<T>(x: Sparse<T>) -> bool {
    pearlite! {
        @(x.n) <= @(x.size)
            && (@x).len() === @(x.size)
            && (@(x.values)).len() === @(x.size)
            && (@(x.idx)).len() === @(x.size)
            && (@(x.back)).len() === @(x.size)
            && forall<i: Int> 0 <= i && i < @(x.n) ==>
            match (@(x.back))[i] {
                j => 0 <= @j && @j < @(x.size)
                    && @((@(x.idx))[@j]) === i
            }
    }
}

/* The methods for accessing and modifying
 */
impl<T> Sparse<T> {
    #[requires(sparse_inv(*self))]
    #[requires(@i < (@self).len())]
    #[ensures(match result {
        None => (@self)[@i] === None,
        Some(x) => (@self)[@i] === Some(*x)
    })]
    #[ensures(match (@self)[@i] {
        None => result === None,
        Some(x) => true // result === Some(x) need 'asref'
    })]
    fn get(&self, i: usize) -> Option<&T> {
        let index = self.idx[i];
        if index < self.n && self.back[index] == i {
            Some(&self.values[i])
        } else {
            None
        }
    }

    // A key lemma to prove for safety of access in `set()`
    // The corresponding proof in Why3 is done as follows.
    //
    // use map.MapInjection as MI
    //
    // lemma permutation :
    //   forall a: sparse_array 'a.
    //    sparse_inv(a) ->
    //    a.card = a.length ->
    //    forall i: int. 0 <= i < a.length -> is_elt a i
    //      by MI.surjective a.back.elts a.card
    //      so exists j. 0 <= j < a.card /\ a.back[j] = i

    #[logic]
    #[requires(sparse_inv(self))]
    #[requires(self.n === self.size)]
    #[requires(0 <= i && i < @(self.size))]
    #[ensures(self.is_elt(i))]
    fn lemma_permutation(self, i: Int) {}

    #[requires(sparse_inv(*self))]
    #[requires(@i < (@*self).len())]
    #[ensures(sparse_inv(^self))]
    #[ensures((@^self).len() === (@*self).len())]
    #[ensures(forall<j: Int> !(j === @i) ==> (@^self)[j] === (@*self)[j])]
    #[ensures((@^self)[@i] === Some(v))]
    fn set(&mut self, i: usize, v: T) {
        self.values[i] = v;
        let index = self.idx[i];
        if !(index < self.n && self.back[index] == i) {
            // the hard assertion!
            proof_assert!(pearlite! {
                {
                    self.lemma_permutation(@i);
                    true
                }
            });
            proof_assert!(@(self.n) < @(self.size));
            // assert!(self.n < self.size);
            self.idx[i] = self.n;
            self.back[self.n] = i;
            self.n += 1;
        }
    }
}

/* The constructor of sparse arrays `sz` is the allocated size,
 * i.e. the valid indexes are 0 to sz-1 `dummy` is a dummy
 * element of type `T`, required because Rust would not accept
 * to create non-initialized arrays.
 */
// #[requires(0 <= @sz)]
#[ensures(sparse_inv(result))]
#[ensures(result.size === sz)]
#[ensures(forall<i: Int> (@result)[i] === None)]
fn create<T: Clone + Copy>(sz: usize, dummy: T) -> Sparse<T> {
    Sparse {
        size: sz,
        n: 0,
        // values : vec![dummy;sz],
        values: vec::from_elem(dummy, sz),
        // idx : vec![0;sz],
        idx: vec::from_elem(0, sz),
        // back : vec![0;sz],
        back: vec::from_elem(0, sz),
    }
}

/* A test program
 */
fn main() {
    let default = 0;
    let mut a = create(10, default);
    let mut b = create(20, default);
    let mut x = a.get(5);
    let mut y = b.get(7);
    // proof_assert!(match x {
    //     None => true,
    //     Some(z) => false
    // });
    proof_assert!(x === None && y === None);
    // assert!(x == None && y == None);
    a.set(5, 1);
    b.set(7, 2);
    x = a.get(5);
    y = b.get(7);
    // proof_assert!(x === Some(1i32));
    // proof_assert!(y === Some(2i32));
    proof_assert!(match x {
        None => false,
        Some(z) => @z === 1
    });
    proof_assert!(match y {
        None => false,
        Some(z) => @z === 2
    });
    // assert!(x == Some(1) && y == Some(2));
    x = a.get(7);
    y = b.get(5);
    proof_assert!(x === None && y === None);
    // assert!(x == None && y == None);
    x = a.get(0);
    y = b.get(0);
    proof_assert!(x === None && y === None);
    // assert!(x == None && y == None);
    x = a.get(9);
    y = b.get(9);
    proof_assert!(x === None && y === None)
    // assert!(x == None && y == None);
}
