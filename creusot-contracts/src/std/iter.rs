use crate::{invariant::*, *};
pub use ::std::iter::*;

mod cloned;
mod copied;
mod empty;
mod enumerate;
mod fuse;
mod map_inv;
mod once;
mod range;
mod repeat;
mod skip;
mod take;
mod zip;

pub use cloned::ClonedExt;
pub use copied::CopiedExt;
pub use enumerate::EnumerateExt;
pub use fuse::FusedIterator;
pub use map_inv::MapInv;
pub use skip::SkipExt;
pub use take::TakeExt;
pub use zip::ZipExt;

pub trait Iterator: ::std::iter::Iterator {
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool;

    #[predicate(prophetic)]
    fn completed(&mut self) -> bool;

    #[law]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self);

    #[law]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);

    #[requires(forall<e : Self::Item, i2 : Self> inv(e) && inv(i2) ==>
                    self.produces(Seq::singleton(e), i2) ==>
                    func.precondition((e, Snapshot::new(Seq::EMPTY))))]
    #[requires(MapInv::<Self, _, F>::reinitialize())]
    #[requires(MapInv::<Self, Self::Item, F>::preservation(self, func))]
    #[ensures(result == MapInv { iter: self, func, produced: Snapshot::new(Seq::EMPTY) })]
    fn map_inv<B, F>(self, func: F) -> MapInv<Self, Self::Item, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Snapshot<Seq<Self::Item>>) -> B,
    {
        MapInv { iter: self, func, produced: snapshot! {Seq::EMPTY} }
    }
}

pub trait IntoIterator: ::std::iter::IntoIterator
where
    Self::IntoIter: Iterator,
{
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate(prophetic)]
    fn into_iter_post(self, res: Self::IntoIter) -> bool;
}

impl<I: Iterator> IntoIterator for I {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
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
                where Self : Iterator {

                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<Self::Item>;

                #[pure]
                #[ensures(result.iter() == self && result.n() == n@)]
                fn skip(self, n: usize) -> Skip<Self>;

                #[pure]
                #[ensures(result.iter() == self && result.n() == n@)]
                fn take(self, n: usize) -> Take<Self>;

                #[pure]
                #[ensures(result.iter() == self)]
                fn cloned<'a, T>(self) -> Cloned<Self>
                    where T : 'a + Clone,
                        Self: Sized + Iterator<Item = &'a T>;

                #[pure]
                #[ensures(result.iter() == self)]
                fn copied<'a, T>(self) -> Copied<Self>
                    where T : 'a + Copy,
                        Self: Sized + Iterator<Item = &'a T>;

                #[pure]
                // These two requirements are here only to prove the absence of overflows
                #[requires(forall<i: &mut Self_> inv(i) && i.completed() ==> i.produces(Seq::EMPTY, ^i))]
                #[requires(forall<s: Seq<Self_::Item>, i: Self_>
                            inv(s) && inv(i) && self.produces(s, i) ==>
                            s.len() < std::usize::MAX@)]
                #[ensures(result.iter() == self && result.n() == 0)]
                fn enumerate(self) -> Enumerate<Self>;

                #[ensures(result@ == Some(self))]
                fn fuse(self) -> Fuse<Self>;

                #[pure]
                #[requires(other.into_iter_pre())]
                #[ensures(result.itera() == self)]
                #[ensures(other.into_iter_post(result.iterb()))]
                fn zip<U: IntoIterator>(self, other: U) -> Zip<Self, U::IntoIter>
                    where U::IntoIter: Iterator;

                // TODO: Investigate why Self_ needed
                #[ensures(exists<done : &mut Self_, prod: Seq<_>>
                    inv(done) && inv(prod) && resolve(&^done) && done.completed() &&
                    self.produces(prod, *done) && B::from_iter_post(prod, result))]
                fn collect<B>(self) -> B
                    where B: FromIterator<Self::Item>;
            }

            trait IntoIterator
                where Self: IntoIterator {

                #[requires(self.into_iter_pre())]
                #[ensures(self.into_iter_post(result))]
                fn into_iter(self) -> Self::IntoIter
                    where Self::IntoIter: Iterator;
            }

            trait FromIterator<A>
                where Self: FromIterator<A> {

                #[requires(iter.into_iter_pre())]
                #[ensures(exists<into_iter: T::IntoIter, done: &mut T::IntoIter, prod: Seq<A>>
                            inv(into_iter) && inv(done) && inv(prod) &&
                            iter.into_iter_post(into_iter) &&
                            into_iter.produces(prod, *done) && done.completed() && resolve(&^done) &&
                            Self_::from_iter_post(prod, result))]
                fn from_iter<T>(iter: T) -> Self
                    where T: IntoIterator<Item = A>, T::IntoIter: Iterator;
            }

            #[pure]
            fn empty<T>() -> Empty<T>;

            #[pure]
            #[ensures(result@ == Some(value))]
            fn once<T>(value: T) -> Once<T>;

            #[pure]
            #[ensures(result@ == elt)]
            fn repeat<T: Clone>(elt: T) -> Repeat<T>;
        }
    }
}
