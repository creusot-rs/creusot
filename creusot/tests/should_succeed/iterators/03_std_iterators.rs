extern crate creusot_contracts;
use creusot_contracts::{logic::Int, std::iter::*, *};

#[requires((@slice).len() < 1000)]
#[ensures(@result == (@slice).len())]
pub fn slice_iter<T>(slice: &[T]) -> usize {
    let mut i = 0;
    #[invariant(dummy, @i == produced.len())]
    for _ in slice.iter() {
        i += 1;
    }
    i
}

#[requires((@vec).len() < 1000)]
#[ensures(@result == (@vec).len())]
pub fn vec_iter<T>(vec: &Vec<T>) -> usize {
    let mut i = 0;
    #[invariant(dummy, @i == produced.len())]
    for _ in vec {
        i += 1;
    }
    i
}

#[ensures((@^v).len() == (@v).len())]
#[ensures(forall<i : _> 0 <= i && i < (@v).len() ==> @(@^v)[i] == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    #[invariant(user, forall<i : Int> 0 <= i && i < produced.len() ==> @^produced[i] == 0)]
    for x in v.iter_mut() {
        *x = 0;
    }
}

#[requires(iter.invariant())]
pub fn skip_take<I: Iterator>(iter: I, n: usize) {
    let res = iter.take(n).skip(n).next();

    proof_assert! { res == None };
}

trait FromIterSpec<A>: FromIterator<A> {
    #[predicate]
    fn from_iter_logic(prod: Seq<A>, res: Self) -> bool;
}

impl<T> FromIterSpec<T> for Vec<T> {
    #[predicate]
    fn from_iter_logic(prod: Seq<T>, res: Self) -> bool {
        pearlite! { prod == @res }
    }
}

use logic::Seq;
use std::iter::FromIterator;

extern_spec! {
    mod std {
        mod iter {
            trait FromIterator<A>
                where Self: FromIterSpec<A> {

            // TODO: Investigate why Self_ needed
            #[ensures(Self_::from_iter_logic(Seq::EMPTY, result))]
            fn from_iter<T>(iter: T) -> Self
                where
                    T: IntoIterator<Item = A>;
            }
            trait Iterator
                where Self : Invariant {
                #[ensures(exists<done_ : &mut Self_, prod: Seq<_>> (^done_).resolve() && done_.completed() && self.produces(prod, *done_) &&
                    B::from_iter_logic(prod, result)
                )]
                fn collect<B>(self) -> B
                    where B : FromIterSpec<Self::Item>;
            }
        }
    }
}

#[requires((@v).len() == 4)]
pub fn counter(v: Vec<u32>) {
    let mut cnt = 0;

    let x: Vec<_> = v
        .iter()
        .map_inv(
            #[requires(@cnt == (*_prod).len() && cnt < usize::MAX)]
            #[ensures(@cnt == @old(cnt) + 1 && @cnt == (*_prod).len() + 1)]
            |x, _prod| {
                cnt += 1;
                x
            },
        )
        .collect();

    proof_assert!{ (@x).len() == 4 };
    proof_assert! { @cnt == 4 };
}
