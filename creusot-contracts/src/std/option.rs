use crate::*;
use ::std::cmp::Ordering;
pub use ::std::option::*;

impl<T: DeepModel> DeepModel for Option<T> {
    type DeepModelTy = Option<T::DeepModelTy>;

    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Some(t) => Some(t.deep_model()),
            None => None,
        }
    }
}

extern_spec! {
    mod std {
        mod option {
            impl<T : PartialEq + DeepModel> PartialEq for Option<T> {
                #[allow(unstable_name_collisions)]
                #[ensures(result == (self.deep_model() == rhs.deep_model()))]
                fn eq(&self, rhs: &Self) -> bool;
            }
        }
    }
}

extern_spec! {
    mod std {
        mod option {
            impl<T> Option<T> {
                #[pure]
                #[ensures(result == (*self != None))]
                fn is_some(&self) -> bool;

                #[pure]
                #[ensures(result == (*self == None))]
                fn is_none(&self) -> bool;

                #[pure]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn unwrap(self) -> T;

                #[pure]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn expect(self, msg: &str) -> T;

                #[pure]
                #[ensures(self == None ==> result == default)]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or(self, default: T) -> T;

                #[pure]
                #[ensures(*self == None ==> result == None && ^self == None)]
                #[ensures(
                    *self == None
                    || exists<r: &mut T> result == Some(r) && *self == Some(*r) && ^self == Some(^r)
                )]
                fn as_mut(&mut self) -> Option<&mut T>;

                #[pure]
                #[ensures(*self == None ==> result == None)]
                #[ensures(
                    *self == None || exists<r: &T> result == Some(r) && *self == Some(*r)
                )]
                fn as_ref(&self) -> Option<&T>;

                #[pure]
                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || result == optb)]
                fn and<U>(self, optb: Option<U>) -> Option<U>;

                #[pure]
                #[ensures(self == None ==> result == optb)]
                #[ensures(self == None || result == self)]
                fn or(self, optb: Option<T>) -> Option<T>;

                #[pure]
                #[ensures(result == *self && ^self == None)]
                fn take(&mut self) -> Option<T>;

                #[pure]
                #[ensures(result == *self && ^self == Some(value))]
                fn replace(&mut self, value: T) -> Option<T>;

                #[ensures(self == None ==> result.is_default())]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or_default(self) -> T
                where
                    T: Default;
            }

            impl<T> Option<&T> {
                #[pure]
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
                #[pure]
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
                #[pure]
                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || self == Some(result))]
                fn flatten(self) -> Option<T>;
            }
        }
    }
}

impl<T> Default for Option<T> {
    #[open]
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == None }
    }
}

impl<T: OrdLogic> OrdLogic for Option<T> {
    #[logic]
    #[open]
    fn cmp_log(self, o: Self) -> Ordering {
        match (self, o) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(x), Some(y)) => x.cmp_log(y),
        }
    }

    ord_laws_impl! {}
}

impl<T> View for IntoIter<T> {
    type ViewTy = Option<T>;

    #[open(self)]
    #[logic]
    #[trusted]
    fn view(self) -> Option<T> {
        pearlite! { absurd }
    }
}

impl<T> Iterator for IntoIter<T> {
    #[predicate(prophetic)]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[law]
    #[open(self)]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<T> IntoIterator for Option<T> {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self == res@ }
    }
}

impl<'a, T> View for Iter<'a, T> {
    type ViewTy = Option<&'a T>;

    #[open(self)]
    #[logic]
    #[trusted]
    fn view(self) -> Option<&'a T> {
        pearlite! { absurd }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    #[predicate(prophetic)]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[law]
    #[open(self)]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> IntoIterator for &'a Option<T> {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! {
            (*self == None ==> res@ == None) &&
            (*self == None || exists<r: &T> res@ == Some(r) && *self == Some(*r))
        }
    }
}

impl<'a, T> View for IterMut<'a, T> {
    type ViewTy = Option<&'a mut T>;

    #[logic]
    #[open(self)]
    #[trusted]
    fn view(self) -> Option<&'a mut T> {
        pearlite! { absurd }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    #[predicate(prophetic)]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[law]
    #[open(self)]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> IntoIterator for &'a mut Option<T> {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate(prophetic)]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! {
            (*self == None ==> res@ == None && ^self == None) &&
            (*self == None || exists<r: &mut T> res@ == Some(r) && *self == Some(*r) && ^self == Some(^r))
        }
    }
}
