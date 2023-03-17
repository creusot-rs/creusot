use crate::{invariant::Invariant, *};
pub use ::std::option::*;

extern_spec! {
    mod std {
        mod option {
            impl<T> Option<T> {
                #[ensures(result == (*self != None))]
                fn is_some(&self) -> bool;

                #[ensures(result == (*self == None))]
                fn is_none(&self) -> bool;

                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn unwrap(self) -> T;

                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn expect(self, msg: &str) -> T;

                #[ensures(self == None ==> result == default)]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or(self, default: T) -> T;

                #[ensures(*self == None ==> result == None && ^self == None)]
                #[ensures(
                    *self == None
                    || exists<r: &mut T> result == Some(r) && *self == Some(*r) && ^self == Some(^r)
                )]
                fn as_mut(&mut self) -> Option<&mut T>;

                #[ensures(*self == None ==> result == None)]
                #[ensures(
                    *self == None || exists<r: &T> result == Some(r) && *self == Some(*r)
                )]
                fn as_ref(&self) -> Option<&T>;

                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || result == optb)]
                fn and<U>(self, optb: Option<U>) -> Option<U>;

                #[ensures(self == None ==> result == optb)]
                #[ensures(self == None || result == self)]
                fn or(self, optb: Option<T>) -> Option<T>;

                #[ensures(result == *self && ^self == None)]
                fn take(&mut self) -> Option<T>;

                #[ensures(result == *self && ^self == Some(value))]
                fn replace(&mut self, value: T) -> Option<T>;

                #[ensures(self == None ==> result.is_default())]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or_default(self) -> T
                where
                    T: Default;
            }

            impl<T> Option<&T> {
                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || exists<t: &T> self == Some(t) && result == Some(*t))]
                fn copied(self) -> Option<T>
                where
                    T: Copy;

                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || exists<t: &T> self == Some(t) && result == Some(*t))]
                fn cloned(self) -> Option<T>
                where
                    T: Clone;
            }

            impl<T> Option<&mut T> {
                #[ensures(self == None ==> result == None)]
                #[ensures(
                    self == None
                    || exists<t: &mut T> self == Some(t) && result == Some(*t) && t.resolve()
                )]
                fn copied(self) -> Option<T>
                where
                    T: Copy;

                #[ensures(self == None ==> result == None)]
                #[ensures(
                    self == None
                    || exists<t: &mut T> self == Some(t) && result == Some(*t) && t.resolve()
                )]
                fn cloned(self) -> Option<T>
                where
                    T: Clone;
            }

            impl<T> Option<Option<T>> {
                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || self == Some(result))]
                fn flatten(self) -> Option<T>;
            }
        }
    }
}

impl<T> Default for Option<T> {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == None }
    }
}

impl<T> ShallowModel for IntoIter<T> {
    type ShallowModelTy = Option<T>;

    #[logic]
    #[trusted]
    fn shallow_model(self) -> Option<T> {
        pearlite! { absurd }
    }
}

impl<T> Invariant for IntoIter<T> {}

impl<T> Iterator for IntoIter<T> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { @*self == None && self.resolve() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> @self == Some(e) && visited == Seq::singleton(e) && @o == None
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<T> IntoIterator for Option<T> {
    #[predicate]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self == @res }
    }
}

impl<'a, T> ShallowModel for Iter<'a, T> {
    type ShallowModelTy = Option<&'a T>;

    #[logic]
    #[trusted]
    fn shallow_model(self) -> Option<&'a T> {
        pearlite! { absurd }
    }
}

impl<'a, T> Invariant for Iter<'a, T> {}

impl<'a, T> Iterator for Iter<'a, T> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { @*self == None && self.resolve() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> @self == Some(e) && visited == Seq::singleton(e) && @o == None
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> IntoIterator for &'a Option<T> {
    #[predicate]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! {
            (*self == None ==> @res == None) &&
            (*self == None || exists<r: &T> @res == Some(r) && *self == Some(*r))
        }
    }
}

impl<'a, T> ShallowModel for IterMut<'a, T> {
    type ShallowModelTy = Option<&'a mut T>;

    #[logic]
    #[trusted]
    fn shallow_model(self) -> Option<&'a mut T> {
        pearlite! { absurd }
    }
}

impl<'a, T> Invariant for IterMut<'a, T> {}

impl<'a, T> Iterator for IterMut<'a, T> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { @*self == None && self.resolve() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> @self == Some(e) && visited == Seq::singleton(e) && @o == None
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> IntoIterator for &'a mut Option<T> {
    #[predicate]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! {
            (*self == None ==> @res == None && ^self == None) &&
            (*self == None || exists<r: &mut T> @res == Some(r) && *self == Some(*r) && ^self == Some(^r))
        }
    }
}
