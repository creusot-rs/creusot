// This example appeared in the following paper:

//     Thierry Hubert and Claude Marché.  Separation analysis for
//     deductive verification.  In Heap Analysis and Verification
//     (HAV'07), pages 81--93, Braga, Portugal, March 2007.
//     http://www.lri.fr/~marche/hubert07hav.pdf

// It is an adaptation of an original Java code given by Peter Mueller
// (Specification and verification challenges. Exploratory Workshop:
// Challenges in Java Program Verification, Nijmegen, The Netherlands,
// 2006), as a challenge for reasoning with memory separation.

// The function `m` below takes a vector `t` as argument, and returns
// a new vector made of only the positive values of `t`. Even the
// absence of panic is tricky to show, in line

//     u[count] = t[i];

// to prove that `count` is not outside the bounds of `u`, ones has to
// specify the functional behavior in terms of number of positive
// elements in the array. Moreover, the verification approach in use
// must be able to automatically know that the newly allocated vector
// is separated from the original one. Thanks to Rust's ownership
// policy, and its supports in Creusot, this separation comes here for
// free.

extern crate creusot_contracts;
use creusot_contracts::{
    logic::{Int, Seq},
    vec, *,
};

// number of positive elements of `t` between `i` (included) and `j`
// (excluded)
#[logic]
#[variant(j-i)]
fn num_of_pos(i: Int, j: Int, t: Seq<i32>) -> Int {
    pearlite! {
        if i >= j { 0 } else {
            if t[j-1]@ > 0 {
                num_of_pos(i,j-1,t) + 1
            } else {
                num_of_pos(i,j-1,t)
            }
        }
    }
}

// original lemmas in the C version, not needed here

// lemma num_of_pos_non_negative{L} :
//   \forall integer i j, int t[]; 0 <= num_of_pos(i,j,t);
//

// lemma num_of_pos_additive{L} :
//   \forall integer i j k, int t[]; i <= j <= k ==>
//       num_of_pos(i,k,t) == num_of_pos(i,j,t) + num_of_pos(j,k,t);
//

// lemma: `num_of_pos` is increasing
#[logic]
#[requires(j <= k)]
#[ensures(num_of_pos(i,j,t) <= num_of_pos(i,k,t))]
#[variant(k-j)]
fn lemma_num_of_pos_increasing(i: Int, j: Int, k: Int, t: Seq<i32>) {
    pearlite! {
        if j < k {
            lemma_num_of_pos_increasing(i,j+1,k,t)
        }
    }
}

// lemma: `num_of_pos` is strictly increasing when a positive element
// is met
#[logic]
#[requires(0 <= i && i < t.len())]
#[requires(t[i]@ > 0)]
#[ensures(num_of_pos(0,i,t) < num_of_pos(0,i+1,t))]
fn lemma_num_of_pos_strictly_increasing(i: Int, t: Seq<i32>) {}

// the main function to prove
pub fn m(t: Vec<i32>) -> Vec<i32> {
    let mut count: usize = 0;
    let mut i: usize = 0;
    #[invariant(i@ <= t@.len())]
    #[invariant(count@ <= i@)]
    #[invariant(count@ == num_of_pos(0,i@,t@))]
    // #[variant(t@.len() - i@)]
    while i < t.len() {
        if t[i] > 0 {
            count += 1
        }
        i += 1;
    }
    let mut u: Vec<i32> = vec![0; count];
    count = 0;

    i = 0;
    #[invariant(count@ == num_of_pos(0,i@,t@))]
    #[invariant(u@.len() == num_of_pos(0,t@.len(),t@))]
    // #[variant(t@.len() - i@)]
    while i < t.len() {
        if t[i] > 0 {
            // the tricky assertions, that needs lemmas
            proof_assert! {
                lemma_num_of_pos_strictly_increasing(i@,u@);
                num_of_pos(0,i@,t@) < num_of_pos(0,i@+1,t@)
            };
            proof_assert! {
                lemma_num_of_pos_increasing(0,i@+1,t@.len(),t@);
                count@ < u@.len()
            };
            u[count] = t[i];
            count += 1;
        }
        i += 1;
    }
    return u;
}

#[trusted]
#[requires(false)]
pub fn main() {
    let mut v = Vec::new();
    v.push(1);
    v.push(-2);
    v.push(3);
    v.push(-4);
    v.push(5);
    let w = m(v);
    println!("w.len = {}", w.len());
    for i in 0..w.len() {
        println!("w[{}] = {}", i, w[i]);
    }
}
