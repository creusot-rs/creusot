use crate::{invariant::Invariant, *};
pub use ::std::iter::*;

mod empty;
mod map_inv;
mod once;
mod range;
mod repeat;
mod skip;
mod take;

pub use map_inv::MapInv;
pub use skip::SkipExt;
pub use take::TakeExt;

pub trait Iterator: ::std::iter::Iterator + Invariant {
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, _: Self) -> bool;

    #[predicate]
    fn completed(&mut self) -> bool;

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self);

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);

    #[requires(forall<e : Self::Item, i2 : Self> i2.invariant() ==> self.produces(Seq::singleton(e), i2) ==> func.precondition((e, Ghost::new(Seq::EMPTY))))]
    #[requires(MapInv::<Self, _, F>::reinitialize())]
    #[requires(MapInv::<Self, Self::Item, F>::preservation(self, func))]
    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    #[ensures(result == MapInv { iter: self, func, produced: Ghost::new(Seq::EMPTY) })]
    fn map_inv<B, F>(self, func: F) -> MapInv<Self, Self::Item, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Ghost<Seq<Self::Item>>) -> B,
    {
        MapInv { iter: self, func, produced: ghost! {Seq::EMPTY} }
    }
}

pub trait IntoIterator: ::std::iter::IntoIterator {
    #[predicate]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    fn into_iter_post(self, res: Self::IntoIter) -> bool;
}

impl<I: Iterator> IntoIterator for I {
    #[predicate]
    fn into_iter_pre(self) -> bool {
        self.invariant()
    }

    #[predicate]
    fn into_iter_post(self, res: Self) -> bool {
        self == res
    }
}

pub trait FromIterator<A>: ::std::iter::FromIterator<A> {
    #[predicate]
    fn from_iter_post(prod: Seq<A>, res: Self) -> bool;
}

extern_spec! {
    mod std {
        mod iter {
            trait Iterator
                where Self : Iterator + Invariant {

                #[requires((*self).invariant())]
                #[ensures((^self).invariant())]
                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<Self::Item>;

                #[requires(self.invariant())]
                #[ensures(result.invariant())]
                #[ensures(result.iter() == self && result.n() == @n)]
                fn skip(self, n: usize) -> Skip<Self>;

                #[requires(self.invariant())]
                #[ensures(result.invariant())]
                #[ensures(result.iter() == self && result.n() == @n)]
                fn take(self, n: usize) -> Take<Self>;

                #[requires(self.invariant())]
                // TODO: Investigate why Self_ needed
                #[ensures(exists<done_ : &mut Self_, prod: Seq<_>> (^done_).resolve() && done_.completed() &&
                    self.produces(prod, *done_) && B::from_iter_post(prod, result))]
                fn collect<B>(self) -> B
                    where B: FromIterator<Self::Item>;
            }

            trait IntoIterator
                where Self: IntoIterator {

                #[requires(self.into_iter_pre())]
                #[ensures(self.into_iter_post(result))]
                #[ensures(result.invariant())]
                fn into_iter(self) -> Self::IntoIter
                    where Self::IntoIter: Iterator + Invariant;
            }

            trait FromIterator<A>
                where Self: FromIterator<A> {

                #[requires(iter.into_iter_pre())]
                #[ensures(exists<into_iter: T::IntoIter, done_: &mut T::IntoIter, prod: Seq<A>>
                              iter.into_iter_post(into_iter) &&
                              into_iter.produces(prod, *done_) && done_.completed() && (^done_).resolve() &&
                              Self_::from_iter_post(prod, result))]
                fn from_iter<T>(iter: T) -> Self
                    where T: IntoIterator<Item = A>, T::IntoIter: Iterator;
            }

            #[ensures(result.invariant())]
            fn empty<T>() -> Empty<T>;

            #[ensures(@result == Some(value))]
            #[ensures(result.invariant())]
            fn once<T>(value: T) -> Once<T>;

            #[ensures(@result == elt)]
            #[ensures(result.invariant())]
            fn repeat<T: Clone>(elt: T) -> Repeat<T>;
        }
    }
}
