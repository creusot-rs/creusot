use crate::*;
pub use ::std::iter::*;

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

pub trait Iterator: ::std::iter::Iterator {
    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool;

    #[logic(prophetic)]
    fn completed(&mut self) -> bool;

    #[law]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self);

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);

    #[check(ghost)]
    #[requires(forall<e, i2>
                    self.produces(Seq::singleton(e), i2) ==>
                    func.precondition((e, Snapshot::new(Seq::empty()))))]
    #[requires(MapInv::<Self, _, F>::reinitialize())]
    #[requires(MapInv::<Self, Self::Item, F>::preservation(self, func))]
    #[ensures(result == MapInv { iter: self, func, produced: Snapshot::new(Seq::empty())})]
    fn map_inv<B, F>(self, func: F) -> MapInv<Self, Self::Item, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, Snapshot<Seq<Self::Item>>) -> B,
    {
        MapInv { iter: self, func, produced: snapshot! {Seq::empty()} }
    }
}

pub trait FromIterator<A>: ::std::iter::FromIterator<A> {
    #[logic]
    fn from_iter_post(prod: Seq<A>, res: Self) -> bool;
}

pub trait DoubleEndedIterator: ::std::iter::DoubleEndedIterator + Iterator {
    #[logic(prophetic)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool;

    #[law]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self);

    #[law]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);
}

extern_spec! {
    mod std {
        mod iter {
            trait Iterator
                where Self: Iterator {

                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<Self::Item>;

                #[check(ghost)]
                #[ensures(result.iter() == self && result.n() == n@)]
                fn skip(self, n: usize) -> Skip<Self>
                    where Self: Sized;

                #[check(ghost)]
                #[ensures(result.iter() == self && result.n() == n@)]
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
                #[requires(forall<e, i2>
                                self.produces(Seq::singleton(e), i2) ==>
                                f.precondition((e,)))]
                #[requires(map::reinitialize::<Self_, B, F>())]
                #[requires(map::preservation::<Self_, B, F>(self, f))]
                #[ensures(result.iter() == self && result.func() == f)]
                fn map<B, F>(self, f: F) -> Map<Self, F>
                    where Self: Sized, F: FnMut(Self_::Item) -> B;

                #[check(ghost)]
                #[requires(filter::immutable(f))]
                #[requires(filter::no_precondition(f))]
                #[requires(filter::precise(f))]
                #[ensures(result.iter() == self && result.func() == f)]
                fn filter<P>(self, f: P) -> Filter<Self, P>
                    where Self: Sized, P: for<'a> FnMut(&Self_::Item) -> bool;

                #[check(ghost)]
                #[requires(filter_map::immutable(f))]
                #[requires(filter_map::no_precondition(f))]
                #[requires(filter_map::precise(f))]
                #[ensures(result.iter() == self && result.func() == f)]
                fn filter_map<B, F>(self, f: F) -> FilterMap<Self, F>
                    where Self: Sized, F: for<'a> FnMut(Self_::Item) -> Option<B>;

                #[check(ghost)]
                // These two requirements are here only to prove the absence of overflows
                #[requires(forall<i: &mut Self_> (*i).completed() ==> (*i).produces(Seq::empty(), ^i))]
                #[requires(forall<s: Seq<Self_::Item>, i: Self_> self.produces(s, i) ==> s.len() < std::usize::MAX@)]
                #[ensures(result.iter() == self && result.n() == 0)]
                fn enumerate(self) -> Enumerate<Self>
                    where Self: Sized;

                #[check(ghost)]
                #[ensures(result@ == Some(self))]
                fn fuse(self) -> Fuse<Self>
                    where Self: Sized;

                #[check(ghost)]
                #[requires(U::into_iter.precondition((other,)))]
                #[ensures(result.itera() == self)]
                #[ensures(U::into_iter.postcondition((other,), result.iterb()))]
                fn zip<U: IntoIterator>(self, other: U) -> Zip<Self, U::IntoIter>
                    where Self: Sized, U::IntoIter: Iterator;

                // TODO: Investigate why Self_ needed
                #[ensures(exists<done: &mut Self_, prod>
                    resolve(^done) && done.completed() && self.produces(prod, *done) && B::from_iter_post(prod, result))]
                fn collect<B>(self) -> B
                    where Self: Sized, B: FromIterator<Self::Item>;

                #[check(ghost)]
                #[ensures(result.iter() == self)]
                fn rev(self) -> Rev<Self>
                    where Self: Sized + DoubleEndedIterator;
            }

            trait FromIterator<A>
                where Self: FromIterator<A> {

                #[requires(T::into_iter.precondition((iter,)))]
                #[ensures(exists<into_iter: T::IntoIter, done: &mut T::IntoIter, prod: Seq<A>>
                            T::into_iter.postcondition((iter,), into_iter) &&
                            into_iter.produces(prod, *done) && done.completed() && resolve(^done) &&
                            Self_::from_iter_post(prod, result))]
                fn from_iter<T>(iter: T) -> Self
                    where Self: Sized, T: IntoIterator<Item = A>, T::IntoIter: Iterator;
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
                where Self: DoubleEndedIterator {
                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces_back(Seq::singleton(v), ^self)
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

impl<I: Iterator + ?Sized> Iterator for &mut I {
    #[open]
    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { (*self).produces(visited, *o) && ^self == ^o }
    }

    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self).completed() && ^*self == ^^self }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
