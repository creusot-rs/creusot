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
use creusot_contracts::{
    logic::{Int, Seq},
    vec, *,
};

/* The sparse array data structure
 */
pub struct Sparse<T> {
    size: usize,      // allocated size
    n: usize,         // number of elements stored so far
    values: Vec<T>,   // actual values at their actual indexes
    idx: Vec<usize>,  // corresponding indexes in `back`
    back: Vec<usize>, // corresponding indexes in `idx`, makes sense between 0 and `n`-1
}

/* The model of the structure is a sequence of optional values
 */
impl<T> ShallowModel for Sparse<T> {
    type ShallowModelTy = Seq<Option<T>>;

    #[ghost]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! {
            Seq::new(self.size@,
                     |i| if self.is_elt(i) { Some(self.values[i]) } else { None })
        }
    }
}

impl<T> Sparse<T> {
    /* The function `s.is_elt(i)` tells whether index `i` points to a
     * existing element. It can be checked as follows:
     *   (1) check that array `idx` maps `i` to a index `j` between 0 and `n` (excluded)
     *   (2) check that `back[j]` is `i`
     */
    #[ghost]
    fn is_elt(&self, i: Int) -> bool {
        pearlite! { self.idx[i]@ < self.n@
                    && self.back[self.idx[i]@]@ == i
        }
    }

    /* The data invariant of the Sparse Array structure
     */
    #[predicate]
    fn sparse_inv(&self) -> bool {
        pearlite! {
            self.n@ <= self.size@
                && self@.len() == self.size@
                && self.values@.len() == self.size@
                && self.idx@.len() == self.size@
                && self.back@.len() == self.size@
                && forall<i: Int> 0 <= i && i < self.n@ ==>
                match self.back[i] {
                    j => 0 <= j@ && j@ < self.size@
                        && self.idx[j@]@ == i
                }
        }
    }

    /* The method for accessing
     */
    #[requires(self.sparse_inv())]
    #[requires(i@ < self@.len())]
    #[ensures(match result {
        None => self@[i@] == None,
        Some(x) => self@[i@] == Some(*x)
    })]
    #[ensures(match self@[i@] {
        None => result == None,
        Some(_) => true // result == Some(x) need 'asref'
    })]
    pub fn get(&self, i: usize) -> Option<&T> {
        let index = self.idx[i];
        if index < self.n && self.back[index] == i {
            Some(&self.values[i])
        } else {
            None
        }
    }

    /* A key lemma to prove for safety of access in `set()`
     */
    #[ghost]
    #[requires(self.sparse_inv())]
    #[requires(self.n == self.size)]
    #[requires(0 <= i && i < self.size@)]
    #[ensures(self.is_elt(i))]
    fn lemma_permutation(self, i: Int) {}

    /* The method for modifying
     */
    #[requires((*self).sparse_inv())]
    #[requires(i@ < self@.len())]
    #[ensures((^self).sparse_inv())]
    #[ensures((^self)@.len() == self@.len())]
    #[ensures(forall<j: Int> 0 <= j && j < self@.len() && j != i@ ==> (^self)@[j] == self@[j])]
    #[ensures((^self)@[i@] == Some(v))]
    pub fn set(&mut self, i: usize, v: T) {
        self.values[i] = v;
        let index = self.idx[i];
        if !(index < self.n && self.back[index] == i) {
            // the hard assertion!
            gh!(Self::lemma_permutation);
            proof_assert!(self.n@ < self.size@);
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
#[ensures(result.sparse_inv())]
#[ensures(result.size == sz)]
#[ensures(forall<i: Int> 0 <= i && i < sz@ ==> result@[i] == None)]
pub fn create<T: Clone + Copy>(sz: usize, dummy: T) -> Sparse<T> {
    Sparse { size: sz, n: 0, values: vec![dummy; sz], idx: vec![0; sz], back: vec![0; sz] }
}

/* A test program
 */
pub fn f() {
    let default = 0;
    let mut a = create(10, default);
    let mut b = create(20, default);
    let mut x = a.get(5);
    let mut y = b.get(7);
    proof_assert!(x == None && y == None);
    // assert!(x == None && y == None);
    a.set(5, 1);
    b.set(7, 2);
    x = a.get(5);
    y = b.get(7);
    proof_assert!(match x {
        None => false,
        Some(z) => z@ == 1
    });
    proof_assert!(match y {
        None => false,
        Some(z) => z@ == 2
    });
    // assert!(x == Some(1) && y == Some(2));
    x = a.get(7);
    y = b.get(5);
    proof_assert!(x == None && y == None);
    // assert!(x == None && y == None);
    x = a.get(0);
    y = b.get(0);
    proof_assert!(x == None && y == None);
    // assert!(x == None && y == None);
    x = a.get(9);
    y = b.get(9);
    proof_assert!(x == None && y == None)
    // assert!(x == None && y == None);
}
