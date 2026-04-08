#[cfg(creusot)]
use crate::mode::Mode;
use crate::prelude::*;
use core::iter::*;

mod cloned;
mod copied;
mod empty;
mod enumerate;
mod filter;
mod filter_map;
mod fuse;
mod map;
mod map_inv;
mod once;
mod range;
mod repeat;
mod rev;
mod skip;
mod take;
mod zip;

pub use cloned::ClonedExt;
pub use copied::CopiedExt;
pub use enumerate::EnumerateExt;
pub use filter::FilterExt;
pub use filter_map::FilterMapExt;
pub use fuse::FusedIterator;
pub use map::MapExt;
pub use map_inv::MapInv;
pub use rev::RevExt;
pub use skip::SkipExt;
pub use take::TakeExt;
pub use zip::ZipExt;

pub trait IteratorSpec: Iterator {
    #[logic(prophetic)]
    fn produces(self, mode: Mode, visited: Seq<Self::Item>, o: Self) -> bool;

    #[logic(prophetic)]
    fn completed(&mut self) -> bool;

    #[logic(law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self);

    #[logic(law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    );

    #[check(ghost)]
    #[requires(|mode| forall<e, i2> self.produces(mode, Seq::singleton(e), i2) && inv(e) ==>
                    func.precondition(mode, (e, Snapshot::new(Seq::empty()))))]
    #[requires(MapInv::<Self, F>::reinitialize())]
    #[requires(forall<mode: Mode> !mode.terminates() ==> MapInv::<Self, F>::preservation(mode, self, func))]
    #[ensures(result == MapInv { iter: self, func, produced: Snapshot::new(Seq::empty())})]
    fn map_inv<B, F>(self, func: F) -> MapInv<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Snapshot<Seq<Self::Item>>) -> B,
    {
        MapInv { iter: self, func, produced: snapshot! {Seq::empty()} }
    }
}

pub trait FromIteratorSpec<A>: FromIterator<A> {
    #[logic]
    fn from_iter_post(mode: Mode, prod: Seq<A>, res: Self) -> bool;
}

impl FromIteratorSpec<()> for () {
    #[logic(open)]
    fn from_iter_post(_: Mode, _: Seq<()>, _res: Self) -> bool {
        true
    }
}

pub trait DoubleEndedIteratorSpec: DoubleEndedIterator + IteratorSpec {
    #[logic(prophetic)]
    fn produces_back(self, mode: Mode, visited: Seq<Self::Item>, o: Self) -> bool;

    #[logic(law)]
    #[ensures(forall<mode: Mode> self.produces_back(mode, Seq::empty(), self))]
    fn produces_back_refl(self);

    #[logic(law)]
    #[requires(a.produces_back(mode, ab, b))]
    #[requires(b.produces_back(mode, bc, c))]
    #[ensures(a.produces_back(mode, ab.concat(bc), c))]
    fn produces_back_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    );
}

extern_spec! {
    mod core {
        mod iter {
            trait Iterator
                where Self: IteratorSpec {

                #[ensures(|result, mode| match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(mode, Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<Self::Item>;

                #[check(ghost)]
                #[ensures(result.iter() == self && result.n() == n)]
                fn skip(self, n: usize) -> Skip<Self>
                    where Self: Sized;

                #[check(ghost)]
                #[ensures(result.iter() == self && result.n() == n)]
                fn take(self, n: usize) -> Take<Self>
                    where Self: Sized;

                #[check(ghost)]
                #[ensures(result.iter() == self)]
                fn cloned<'a, T>(self) -> Cloned<Self>
                    where T: 'a + Clone,
                        Self: Sized + Iterator<Item = &'a T>;

                #[check(ghost)]
                #[ensures(result.iter() == self)]
                fn copied<'a, T>(self) -> Copied<Self>
                    where T: 'a + Copy,
                        Self: Sized + Iterator<Item = &'a T>;

                #[check(ghost)]
                #[requires(forall<mode: Mode, e, i2>
                    !mode.terminates() && self.produces(mode, Seq::singleton(e), i2) && inv(e)
                    ==> f.precondition(mode, (e,)))]
                #[requires(map::reinitialize::<Self, B, F>())]
                #[requires(map::preservation::<Self, B, F>(self, f))]
                #[ensures(result.iter() == self && result.func() == f)]
                fn map<B, F>(self, f: F) -> Map<Self, F>
                    where Self: Sized, F: FnMut(Self::Item) -> B;

                #[check(ghost)]
                #[requires(filter::immutable(f))]
                #[requires(filter::no_precondition(f))]
                #[requires(filter::precise(f))]
                #[ensures(result.iter() == self && result.func() == f)]
                fn filter<P>(self, f: P) -> Filter<Self, P>
                    where Self: Sized, P: for<'a> FnMut(&Self::Item) -> bool;

                #[check(ghost)]
                #[requires(filter_map::immutable(f))]
                #[requires(filter_map::no_precondition(f))]
                #[requires(filter_map::precise(f))]
                #[ensures(result.iter() == self && result.func() == f)]
                fn filter_map<B, F>(self, f: F) -> FilterMap<Self, F>
                    where Self: Sized, F: for<'a> FnMut(Self::Item) -> Option<B>;

                #[check(ghost)]
                // These two requirements are here only to prove the absence of overflows
                #[requires(forall<mode: Mode, i: &mut Self> !mode.terminates() && (*i).completed() ==> (*i).produces(mode, Seq::empty(), ^i))]
                #[requires(forall<mode: Mode, s: Seq<Self::Item>, i: Self> self.produces(mode, s, i) ==> s.len() < core::usize::MAX@)]
                #[ensures(result.iter() == self && result.n()@ == 0)]
                fn enumerate(self) -> Enumerate<Self>
                    where Self: Sized;

                #[check(ghost)]
                #[ensures(result@ == Some(self))]
                fn fuse(self) -> Fuse<Self>
                    where Self: Sized;

                #[check(ghost)]
                #[requires(|mode| U::into_iter.precondition(mode, (other,)))]
                #[ensures(result.itera() == self)]
                #[ensures(|result, mode| U::into_iter.postcondition(mode, (other,), result.iterb()))]
                fn zip<U: IntoIterator>(self, other: U) -> Zip<Self, U::IntoIter>
                    where Self: Sized, U::IntoIter: Iterator;

                #[ensures(|result, mode| exists<done: &mut Self, prod>
                    resolve(^done) && done.completed() && self.produces(mode, prod, *done) && B::from_iter_post(mode, prod, result))]
                fn collect<B>(self) -> B
                    where Self: Sized, B: FromIteratorSpec<Self::Item>;

                #[check(ghost)]
                #[ensures(result.iter() == self)]
                fn rev(self) -> Rev<Self>
                    where Self: Sized + DoubleEndedIteratorSpec;
            }

            trait FromIterator<A>
                where Self: FromIteratorSpec<A> {

                #[requires(|mode| T::into_iter.precondition(mode, (iter,)))]
                #[ensures(|result, mode| exists<into_iter: T::IntoIter, done: &mut T::IntoIter, prod: Seq<A>>
                            T::into_iter.postcondition(mode, (iter,), into_iter) &&
                            into_iter.produces(mode, prod, *done) && done.completed() && resolve(^done) &&
                            Self::from_iter_post(mode, prod, result))]
                fn from_iter<T>(iter: T) -> Self
                    where Self: Sized, T: IntoIterator<Item = A>, T::IntoIter: IteratorSpec;
            }

            #[check(ghost)]
            fn empty<T>() -> Empty<T>;

            #[check(ghost)]
            #[ensures(result@ == Some(value))]
            fn once<T>(value: T) -> Once<T>;

            #[check(ghost)]
            #[ensures(result@ == elt)]
            fn repeat<T: Clone>(elt: T) -> Repeat<T>;

            trait DoubleEndedIterator
                where Self: DoubleEndedIteratorSpec {
                #[ensures(|result, mode| match result {
                    None => self.completed(),
                    Some(v) => (*self).produces_back(mode, Seq::singleton(v), ^self)
                })]
                fn next_back(&mut self) -> Option<Self::Item>;
            }
        }
    }

    impl<I: Iterator> IntoIterator for I {
        #[check(ghost)]
        #[ensures(result == self)]
        fn into_iter(self) -> I;
    }
}

impl<I: IteratorSpec + ?Sized> IteratorSpec for &mut I {
    #[logic(open, prophetic)]
    fn produces(self, mode: Mode, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { (*self).produces(mode, visited, *o) && ^self == ^o }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self).completed() && ^*self == ^^self }
    }

    #[logic(open, law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
    }
}
