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
#[cfg(creusot)]
use creusot_contracts::resolve::structural_resolve;
use creusot_contracts::{
    logic::{FSet, Int, Seq},
    *,
};

/* The sparse array data structure
 */
pub struct Sparse<T, const SIZE: usize> {
    n: usize,            // number of elements stored so far
    values: [T; SIZE],   // actual values at their actual indexes
    idx: [usize; SIZE],  // corresponding indexes in `back`
    back: [usize; SIZE], // corresponding indexes in `idx`, makes sense between 0 and `n`-1
}

/* The model of the structure is a sequence of optional values
 */
impl<T, const SIZE: usize> View for Sparse<T, SIZE> {
    type ViewTy = Seq<Option<T>>;

    #[logic(open(self))]
    #[ensures(result.len() == SIZE@)]
    fn view(self) -> Self::ViewTy {
        pearlite! {
            Seq::create(SIZE@,
                     |i| if self.is_elt(i) { Some(self.values[i]) } else { None })
        }
    }
}

impl<T, const SIZE: usize> Resolve for Sparse<T, SIZE> {
    #[logic(open, prophetic)]
    fn resolve(self) -> bool {
        pearlite! {
            forall<i> 0 <= i && i < SIZE@ ==> resolve(self@[i])
        }
    }

    #[logic(open, prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T, const SIZE: usize> Invariant for Sparse<T, SIZE> {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! {
            self.n@ <= SIZE@
                && forall<i> 0 <= i && i < self.n@ ==>
                { let j = self.back[i];
                  0 <= j@ && j@ < SIZE@ && self.idx[j@]@ == i }
        }
    }
}

impl<T, const SIZE: usize> Sparse<T, SIZE> {
    /* The function `s.is_elt(i)` tells whether index `i` points to a
     * existing element. It can be checked as follows:
     *   (1) check that array `idx` maps `i` to a index `j` between 0 and `n` (excluded)
     *   (2) check that `back[j]` is `i`
     */
    #[logic]
    fn is_elt(&self, i: Int) -> bool {
        pearlite! { self.idx[i]@ < self.n@ && self.back[self.idx[i]@]@ == i }
    }

    /* The method for accessing
     */
    #[requires(i@ < SIZE@)]
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
        if index < self.n && self.back[index] == i { Some(&self.values[i]) } else { None }
    }

    /* A key lemma to prove for safety of access in `set()`
     */
    #[logic]
    #[requires(inv(self))]
    #[requires(self.n == SIZE)]
    #[requires(0 <= i && i < SIZE@)]
    #[ensures(self.is_elt(i))]
    fn lemma_permutation(self, i: Int) {
        self.lemma_permutation_aux(FSet::empty(), i, i);
    }

    #[logic]
    #[variant(SIZE@ - seen.len())]
    #[requires(inv(self))]
    #[requires(self.n == SIZE)]
    #[requires(0 <= cur && cur < SIZE@)]
    #[requires(forall<k> seen.contains(k) ==>
        0 <= k && k < SIZE@ &&
        (k == i || seen.contains(self.idx[k]@)))]
    #[requires(i == cur || (seen.contains(i) && seen.contains(self.idx[cur]@)))]
    #[requires(!seen.contains(cur))]
    #[ensures(0 <= result && result < SIZE@)]
    #[ensures(self.back[result]@ == i)]
    fn lemma_permutation_aux(self, seen: FSet<Int>, i: Int, cur: Int) -> Int {
        pearlite! {
            if self.back[cur]@ == i {
                cur
            } else {
                Self::bounded_fset_len(seen, SIZE@);
                self.lemma_permutation_aux(seen.insert(cur), i, self.back[cur]@)
            }
        }
    }

    #[logic]
    #[variant(bnd)]
    #[requires(forall<x> s.contains(x) ==> 0 <= x && x < bnd)]
    #[requires(bnd >= 0)]
    #[ensures(s.len() <= bnd)]
    fn bounded_fset_len(s: FSet<Int>, bnd: Int) {
        if bnd > 0 {
            Self::bounded_fset_len(s.remove(bnd - 1), bnd - 1)
        }
    }

    /* The method for modifying
     */
    #[requires(i@ < SIZE@)]
    #[ensures(forall<j> 0 <= j && j < SIZE@ && j != i@ ==> (^self)@[j] == self@[j])]
    #[ensures((^self)@[i@] == Some(v))]
    pub fn set(&mut self, i: usize, v: T) {
        self.values[i] = v;
        let index = self.idx[i];
        if !(index < self.n && self.back[index] == i) {
            // the hard assertion!
            snapshot!(Self::lemma_permutation);
            proof_assert!(self.n@ < SIZE@);
            // assert!(self.n < SIZE);
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
#[ensures(forall<i> 0 <= i && i < SIZE@ ==> result@[i] == None)]
pub fn create<T: Copy, const SIZE: usize>(dummy: T) -> Sparse<T, SIZE> {
    Sparse { n: 0, values: [dummy; SIZE], idx: [0; SIZE], back: [0; SIZE] }
}

/* A test program
 */
pub fn f() {
    let default = 0;
    let mut a = create::<_, 10>(default);
    let mut b = create::<_, 20>(default);
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
