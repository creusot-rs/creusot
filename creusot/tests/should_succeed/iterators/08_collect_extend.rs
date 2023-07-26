extern crate creusot_contracts;

use creusot_contracts::{
    invariant::{inv, Invariant},
    logic::{Int, Seq},
    std::*,
    *,
};

// Modeling `extend`.
//
// pub trait Extend<A> {
//     fn extend<T>(&mut self, iter: T)
//     where
//         T: IntoIterator<Item = A>;

//     fn extend_one(&mut self, item: A) { ... }
//     fn extend_reserve(&mut self, additional: usize) { ... }
// }
//
// Here we prove the specific instance of `extend` for `Vec<T>`.
#[requires(inv((*vec)@) && inv((^vec)@))]
#[ensures(
  exists<done_ : &mut I, prod: Seq<_>>
    done_.completed() && iter.produces(prod, *done_) && (^vec)@ == vec@.concat(prod)
)]
pub fn extend<T, I: Iterator<Item = T> + Invariant>(vec: &mut Vec<T>, iter: I) {
    let old_vec = gh! { vec };
    #[invariant(^*old_vec == ^vec)]
    #[invariant(vec@.ext_eq(old_vec@.concat(*produced)))]
    for x in iter {
        vec.push(x);
    }
}

// fn collect<B>(self) -> B where
//     B: FromIterator<Self::Item>,
//
//  We prove the specific instance for vector
#[ensures(
  exists<done_ : &mut I, prod: Seq<_>>
    done_.completed() && iter.produces(prod, *done_) && result@ == prod
)]
pub fn collect<I: Iterator>(iter: I) -> Vec<I::Item> {
    let mut res = Vec::new();

    #[invariant(res@.ext_eq(*produced))]
    for x in iter {
        res.push(x);
    }
    res
}

pub fn extend_index(mut v1: Vec<u32>, v2: Vec<u32>) {
    let oldv1 = gh! { *v1 };
    let oldv2 = gh! { *v2 };
    extend(&mut v1, v2.into_iter());

    proof_assert! { v1@.ext_eq(oldv1@.concat(oldv2@)) };
}

#[requires(forall<prod : Seq<u32>, fin: I> iter.produces(prod, fin) ==> forall<i : _> 0 <= i && i < prod.len() ==> prod[i]@ == i)]
pub fn collect_example<I: Iterator<Item = u32>>(iter: I) {
    let v: Vec<u32> = collect(iter);

    proof_assert! { forall<i : Int> 0 <= i && i < v@.len() ==> v[i]@ == i };
}
