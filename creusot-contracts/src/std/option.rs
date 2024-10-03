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

                #[requires(match self {
                    None => true,
                    Some(t) => f.precondition((t,)),
                })]
                #[ensures(match self {
                    None => result == false,
                    Some(t) => resolve(&t) && f.postcondition_once((t,), result),
                })]
                fn is_some_and(self, f: impl FnOnce(T) -> bool) -> bool;

                #[pure]
                #[ensures(result == (*self == None))]
                fn is_none(&self) -> bool;

                #[pure]
                #[ensures(*self == None ==> result == None)]
                #[ensures(
                    *self == None || exists<r: &T> result == Some(r) && *self == Some(*r)
                )]
                fn as_ref(&self) -> Option<&T>;

                #[pure]
                #[ensures(*self == None ==> result == None && ^self == None)]
                #[ensures(
                    *self == None
                    || exists<r: &mut T> result == Some(r) && *self == Some(*r) && ^self == Some(^r)
                )]
                fn as_mut(&mut self) -> Option<&mut T>;

                #[pure]
                #[ensures(match *self {
                    None => result@.len() == 0,
                    Some(t) => result@.len() == 1 && result@[0] == t
                })]
                fn as_slice(&self) -> &[T];

                #[pure]
                #[ensures(match *self {
                    None => result@.len() == 0,
                    Some(_) => exists<b:&mut T> *self == Some(*b) && ^self == Some(^b) && (*result)@[0] == *b && (^result)@[0] == ^b,
                })]
                fn as_mut_slice(&mut self) -> &mut [T];

                #[pure]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn expect(self, msg: &str) -> T;

                #[pure]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn unwrap(self) -> T;

                #[pure]
                #[ensures(self == None ==> result == default)]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or(self, default: T) -> T;

                #[requires(self == None ==> f.precondition(()))]
                #[ensures(match self {
                    None => f.postcondition_once((), result),
                    Some(t) => result == t
                })]
                fn unwrap_or_else<F>(self, f: F) -> T
                where
                    F: FnOnce() -> T;

                #[ensures(self == None ==> result.is_default())]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or_default(self) -> T
                where
                    T: Default;

                #[pure]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                unsafe fn unwrap_unchecked(self) -> T;

                #[requires(match self {
                    None => true,
                    Some(t) => f.precondition((t,)),
                })]
                #[ensures(match self {
                    None => result == None,
                    Some(t) => exists<r: _> result == Some(r) && f.postcondition_once((t,), r),
                })]
                fn map<U, F>(self, f: F) -> Option<U>
                where
                    F: FnOnce(T) -> U;

                #[requires(match self {
                    None => true,
                    Some(t) => f.precondition((&t,)),
                })]
                #[ensures(result == self)]
                #[ensures(match self {
                    None => true,
                    Some(t) => f.postcondition_once((&t,), ()),
                })]
                fn inspect<F>(self, f: F) -> Option<T>
                where
                    F: FnOnce(&T);

                #[requires(match self {
                    None => true,
                    Some(t) => f.precondition((t,)),
                })]
                #[ensures(match self {
                    None => result == default,
                    Some(t) => f.postcondition_once((t,), result)
                })]
                fn map_or<U, F>(self, default: U, f: F) -> U
                where
                    F: FnOnce(T) -> U;

                #[requires(match self {
                    None => default.precondition(()),
                    Some(t) => f.precondition((t,)),
                })]
                #[ensures(match self {
                    None => default.postcondition_once((), result),
                    Some(t) => f.postcondition_once((t,), result),
                })]
                fn map_or_else<U, D, F>(self, default: D, f: F) -> U
                where
                    D: FnOnce() -> U,
                    F: FnOnce(T) -> U;

                #[ensures(match self {
                    None => result == Err(err),
                    Some(t) => result == Ok(t),
                })]
                fn ok_or<E>(self, err: E) -> Result<T, E>;

                #[requires(self == None ==> err.precondition(()))]
                #[ensures(match self {
                    None => exists<r: _> result == Err(r) && err.postcondition_once((), r),
                    Some(t) => result == Ok(t),
                })]
                fn ok_or_else<E, F>(self, err: F) -> Result<T, E>
                where
                    F: FnOnce() -> E;

                #[ensures(match *self {
                    None => result == None,
                    Some(t) => result == Some(&t.deref()),
                })]
                fn as_deref(&self) -> Option<&<T as ::std::ops::Deref>::Target>
                where
                    T: ::std::ops::Deref;

                #[pure]
                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || (result == optb && self.resolve()))]
                fn and<U>(self, optb: Option<U>) -> Option<U>;

                #[requires(match self {
                    None => true,
                    Some(t) => f.precondition((t,)),
                })]
                #[ensures(match self {
                    None => result == None,
                    Some(t) => f.postcondition_once((t,), result),
                })]
                fn and_then<U, F>(self, f: F) -> Option<U>
                where
                    F: FnOnce(T) -> Option<U>;

                #[requires(match self {
                    None => true,
                    Some(t) => predicate.precondition((&t,))
                })]
                #[ensures(match self {
                    None => result == None,
                    Some(t) => match result {
                        None => predicate.postcondition_once((&t,), false) && resolve(&t),
                        Some(r) => predicate.postcondition_once((&t,), true) && r == t,
                    },
                })]
                fn filter<P>(self, predicate: P) -> Option<T>
                where
                    P: FnOnce(&T) -> bool;

                #[pure]
                #[ensures(self == None ==> result == optb)]
                #[ensures(self == None || (result == self && optb.resolve()))]
                fn or(self, optb: Option<T>) -> Option<T>;

                #[requires(self == None ==> f.precondition(()))]
                #[ensures(match self {
                    None => f.postcondition_once((), result),
                    Some(t) => result == Some(t),
                })]
                fn or_else<F>(self, f: F) -> Option<T>
                where
                    F: FnOnce() -> Option<T>;

                #[pure]
                #[ensures(match (self, optb) {
                    (None, None)         => result == None,
                    (Some(t1), Some(t2)) => result == None && resolve(&t1) && resolve(&t2),
                    (Some(t), None)      => result == Some(t),
                    (None, Some(t))      => result == Some(t),
                })]
                fn xor(self, optb: Option<T>) -> Option<T>;

                #[pure]
                #[ensures(match *self {
                    Some(t) => resolve(&t),
                    None => true,
                })]
                #[ensures(*result == value && ^self == Some(^result))]
                fn insert(&mut self, value: T) -> &mut T;

                #[pure]
                #[ensures(match *self {
                    None => *result == value && ^self == Some(^result),
                    Some(_) => *self == Some(*result) && ^self == Some(^result) && resolve(&value),
                })]
                fn get_or_insert(&mut self, value: T) -> &mut T;

                #[requires(*self == None ==> f.precondition(()))]
                #[ensures(match *self {
                    None => f.postcondition_once((), *result) && ^self == Some(^result),
                    Some(_) => *self == Some(*result) && ^self == Some(^result),
                })]
                fn get_or_insert_with<F>(&mut self, f: F) -> &mut T
                where
                    F: FnOnce() -> T;

                #[pure]
                #[ensures(result == *self && ^self == None)]
                fn take(&mut self) -> Option<T>;

                #[requires(match *self {
                    None => true,
                    Some(t) => forall<b:&mut T> inv(b) && *b == t ==> predicate.precondition((b,)),
                })]
                #[ensures(match *self {
                    None => result == None && ^self == None,
                    Some(cur) =>
                        exists<b: &mut T, res: bool> cur == *b && predicate.postcondition_once((b,), res) &&
                            if res {
                                ^self == None && result == Some(^b)
                            } else {
                                ^self == Some(^b) && result == None
                            }
                })]
                fn take_if<P>(&mut self, predicate: P) -> Option<T>
                where
                    P: FnOnce(&mut T) -> bool;

                #[pure]
                #[ensures(result == *self && ^self == Some(value))]
                fn replace(&mut self, value: T) -> Option<T>;

                #[pure]
                #[ensures(match (self, other) {
                    (None, _)          => result == None && other.resolve(),
                    (_, None)          => result == None && self.resolve(),
                    (Some(t), Some(u)) => result == Some((t, u)),
                })]
                fn zip<U>(self, other: Option<U>) -> Option<(T, U)>;
            }

            impl<T, U> Option<(T, U)> {
                #[pure]
                #[ensures(match self {
                    None => result == (None, None),
                    Some((t, u)) => result == (Some(t), Some(u)),
                })]
                fn unzip(self) -> (Option<T>, Option<U>);
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

            impl<T, E> Option<Result<T, E>> {
                #[pure]
                #[ensures(match self {
                    None => result == Ok(None),
                    Some(Ok(ok)) => result == Ok(Some(ok)),
                    Some(Err(err)) => result == Err(err),
                })]
                fn transpose(self) -> Result<Option<T>, E>;
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
