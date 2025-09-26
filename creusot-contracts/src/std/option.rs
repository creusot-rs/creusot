use crate::{logic::Mapping, *};
#[cfg(creusot)]
use crate::{logic::such_that, resolve::structural_resolve};
use ::std::cmp::Ordering;
#[cfg(creusot)]
use ::std::marker::Destruct;
pub use ::std::option::*;

impl<T: DeepModel> DeepModel for Option<T> {
    type DeepModelTy = Option<T::DeepModelTy>;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Some(t) => Some(t.deep_model()),
            None => None,
        }
    }
}

extern_spec! {
    impl<T: PartialEq + DeepModel> PartialEq for Option<T> {
        #[allow(unstable_name_collisions)]
        #[ensures(result == (self.deep_model() == rhs.deep_model()))]
        fn eq(&self, rhs: &Self) -> bool {
            match (self, rhs) {
                (None, None) => true,
                (Some(x), Some(y)) => x == y,
                _ => false,
            }
        }
    }

    impl<T: Clone> Clone for Option<T> {
        #[ensures(match (*self, result) {
            (None, None) => true,
            (Some(s), Some(r)) => T::clone.postcondition((&s,), r),
            _ => false
        })]
        fn clone(&self) -> Option<T> {
            match self {
                None => None,
                Some(x) => Some(x.clone())
            }
        }
    }

    mod std {
        mod option {
            impl<T> Option<T> {
                #[check(ghost)]
                #[erasure]
                #[ensures(result == (*self != None))]
                fn is_some(&self) -> bool {
                    match *self {
                        Some(_) => true,
                        None => false,
                    }
                }

                #[erasure]
                #[requires(match self {
                    None => true,
                    Some(t) => f.precondition((t,)),
                })]
                #[ensures(match self {
                    None => result == false,
                    Some(t) => f.postcondition_once((t,), result),
                })]
                fn is_some_and(self, f: impl FnOnce(T) -> bool + Destruct) -> bool {
                    match self {
                        None => false,
                        Some(t) => f(t),
                    }
                }

                #[check(ghost)]
                #[erasure]
                #[ensures(result == (*self == None))]
                fn is_none(&self) -> bool {
                    !self.is_some()
                }

                #[check(ghost)]
                #[erasure]
                #[ensures(*self == None ==> result == None)]
                #[ensures(
                    *self == None || exists<r: &T> result == Some(r) && *self == Some(*r)
                )]
                fn as_ref(&self) -> Option<&T> {
                    match *self {
                        Some(ref t) => Some(t),
                        None => None,
                    }
                }

                #[check(ghost)]
                #[erasure]
                #[ensures(*self == None ==> result == None && ^self == None)]
                #[ensures(
                    *self == None
                    || exists<r: &mut T> result == Some(r) && *self == Some(*r) && ^self == Some(^r)
                )]
                fn as_mut(&mut self) -> Option<&mut T> {
                    match *self {
                        Some(ref mut t) => Some(t),
                        None => None,
                    }
                }

                #[check(ghost)]
                #[ensures(match *self {
                    None => result@.len() == 0,
                    Some(t) => result@.len() == 1 && result@[0] == t
                })]
                fn as_slice(&self) -> &[T] {
                    match self {
                        None => &[],
                        Some(t) => std::slice::from_ref(t),
                    }
                }

                #[check(ghost)]
                #[ensures(match *self {
                    None => result@.len() == 0,
                    Some(_) => exists<b:&mut T>
                        *self == Some(*b) && ^self == Some(^b) &&
                        (*result)@[0] == *b && (^result)@[0] == ^b &&
                        (*result)@.len() == 1 && (^result)@.len() == 1,
                })]
                fn as_mut_slice(&mut self) -> &mut [T] {
                    match self {
                        None => &mut [],
                        Some(t) => std::slice::from_mut(t),
                    }
                }

                #[check(ghost)]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn expect(self, msg: &str) -> T {
                    match self {
                        None => panic!(),
                        Some(t) => t,
                    }
                }

                #[check(ghost)]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn unwrap(self) -> T {
                    match self {
                        None => panic!(),
                        Some(t) => t,
                    }
                }

                #[check(ghost)]
                #[erasure]
                #[ensures(self == None ==> result == default)]
                #[ensures(self == None || (self == Some(result) && resolve(default)))]
                fn unwrap_or(self, default: T) -> T {
                    match self {
                        Some(t) => t,
                        None => default,
                    }
                }

                #[erasure]
                #[requires(self == None ==> f.precondition(()))]
                #[ensures(match self {
                    None => f.postcondition_once((), result),
                    Some(t) => result == t
                })]
                fn unwrap_or_else<F>(self, f: F) -> T
                where
                    F: FnOnce() -> T {
                    match self {
                        Some(t) => t,
                        None => f(),
                    }
                }

                #[erasure]
                #[ensures(self == None ==> T::default.postcondition((), result))]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or_default(self) -> T
                where
                    T: Default {
                    match self {
                        Some(t) => t,
                        None => T::default(),
                    }
                }

                #[check(ghost)]
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                unsafe fn unwrap_unchecked(self) -> T {
                    match self {
                        None => panic!(),
                        Some(t) => t,
                    }
                }

                #[erasure]
                #[requires(match self {
                    None => true,
                    Some(t) => f.precondition((t,)),
                })]
                #[ensures(match self {
                    None => result == None,
                    Some(t) => exists<r> result == Some(r) && f.postcondition_once((t,), r),
                })]
                fn map<U, F>(self, f: F) -> Option<U>
                where
                    F: FnOnce(T) -> U {
                    match self {
                        Some(t) => Some(f(t)),
                        None => None,
                    }
                }

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
                    F: FnOnce(&T) {
                    match self {
                        None => None,
                        Some(t) => { f(&t); Some(t) }
                    }
                }

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
                    F: FnOnce(T) -> U {
                    match self {
                        None => default,
                        Some(t) => f(t),
                    }
                }

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
                    F: FnOnce(T) -> U {
                    match self {
                        None => default(),
                        Some(t) => f(t),
                    }
                }

                #[check(ghost)]
                #[ensures(match self {
                    None => result == Err(err),
                    Some(t) => result == Ok(t) && resolve(err),
                })]
                fn ok_or<E>(self, err: E) -> Result<T, E> {
                    match self {
                        None => Err(err),
                        Some(t) => Ok(t),
                    }
                }

                #[requires(self == None ==> err.precondition(()))]
                #[ensures(match self {
                    None => exists<r> result == Err(r) && err.postcondition_once((), r),
                    Some(t) => result == Ok(t),
                })]
                fn ok_or_else<E, F>(self, err: F) -> Result<T, E>
                where
                    F: FnOnce() -> E {
                    match self {
                        None => Err(err()),
                        Some(t) => Ok(t),
                    }
                }

                #[check(ghost)]
                #[ensures(self == None ==> result == None && optb.resolve())]
                #[ensures(self == None || (result == optb && self.resolve()))]
                fn and<U>(self, optb: Option<U>) -> Option<U> {
                    match self {
                        None => None,
                        Some(_) => optb,
                    }
                }

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
                    F: FnOnce(T) -> Option<U> {
                    match self {
                        None => None,
                        Some(t) => f(t),
                    }
                }

                #[requires(match self {
                    None => true,
                    Some(t) => predicate.precondition((&t,))
                })]
                #[ensures(match self {
                    None => result == None,
                    Some(t) => match result {
                        None => predicate.postcondition_once((&t,), false) && resolve(t),
                        Some(r) => predicate.postcondition_once((&t,), true) && r == t,
                    },
                })]
                fn filter<P>(self, predicate: P) -> Option<T>
                where
                    P: FnOnce(&T) -> bool {
                    match self {
                        None => None,
                        Some(t) => if predicate(&t) { Some(t) } else { None }
                    }
                }

                #[check(ghost)]
                #[ensures(self == None ==> result == optb)]
                #[ensures(self == None || (result == self && optb.resolve()))]
                fn or(self, optb: Option<T>) -> Option<T> {
                    match self {
                        None => optb,
                        Some(t) => Some(t),
                    }
                }

                #[requires(self == None ==> f.precondition(()))]
                #[ensures(match self {
                    None => f.postcondition_once((), result),
                    Some(t) => result == Some(t),
                })]
                fn or_else<F>(self, f: F) -> Option<T>
                where
                    F: FnOnce() -> Option<T> {
                    match self {
                        None => f(),
                        Some(t) => Some(t),
                    }
                }

                #[check(ghost)]
                #[ensures(match (self, optb) {
                    (None, None)         => result == None,
                    (Some(t1), Some(t2)) => result == None && resolve(t1) && resolve(t2),
                    (Some(t), None)      => result == Some(t),
                    (None, Some(t))      => result == Some(t),
                })]
                fn xor(self, optb: Option<T>) -> Option<T> {
                    match (self, optb) {
                        (Some(t), None) | (None, Some(t)) => Some(t),
                        _ => None,
                    }
                }

                #[check(ghost)]
                #[ensures(match *self {
                    Some(t) => resolve(t),
                    None => true,
                })]
                #[ensures(*result == value && ^self == Some(^result))]
                fn insert(&mut self, value: T) -> &mut T {
                    *self = Some(value);
                    match self {
                        None => unreachable!(),
                        Some(v) => v,
                    }
                }

                #[check(ghost)]
                #[ensures(match *self {
                    None => *result == value && ^self == Some(^result),
                    Some(_) => *self == Some(*result) && ^self == Some(^result) && resolve(value),
                })]
                fn get_or_insert(&mut self, value: T) -> &mut T {
                    match self {
                        None => *self = Some(value),
                        Some(_) => {}
                    }
                    match self {
                        None => unreachable!(),
                        Some(v) => v,
                    }
                }

                #[requires(*self == None ==> f.precondition(()))]
                #[ensures(match *self {
                    None => f.postcondition_once((), *result) && ^self == Some(^result),
                    Some(_) => *self == Some(*result) && ^self == Some(^result),
                })]
                fn get_or_insert_with<F>(&mut self, f: F) -> &mut T
                where
                    F: FnOnce() -> T {
                    match self {
                        None => { *self = Some(f()); self.as_mut().unwrap() }
                        Some(t) => t,
                    }
                }

                #[check(ghost)]
                #[ensures(result == *self && ^self == None)]
                fn take(&mut self) -> Option<T> {
                    std::mem::replace(self, None)
                }

                #[requires(match *self {
                    None => true,
                    Some(t) => forall<b:&mut T> inv(b) && *b == t ==> predicate.precondition((b,)),
                })]
                #[ensures(match *self {
                    None => result == None && ^self == None,
                    Some(cur) =>
                        exists<b: &mut T, res: bool> inv(b) && cur == *b && predicate.postcondition_once((b,), res) &&
                            if res {
                                ^self == None && result == Some(^b)
                            } else {
                                ^self == Some(^b) && result == None
                            }
                })]
                fn take_if<P>(&mut self, predicate: P) -> Option<T>
                where
                    P: FnOnce(&mut T) -> bool {
                    match self {
                        None => None,
                        Some(t) => if predicate(t) { self.take() } else { None },
                    }
                }

                #[check(ghost)]
                #[ensures(result == *self && ^self == Some(value))]
                fn replace(&mut self, value: T) -> Option<T> {
                    std::mem::replace(self, Some(value))
                }

                #[check(ghost)]
                #[ensures(match (self, other) {
                    (None, _)          => result == None && other.resolve(),
                    (_, None)          => result == None && self.resolve(),
                    (Some(t), Some(u)) => result == Some((t, u)),
                })]
                fn zip<U>(self, other: Option<U>) -> Option<(T, U)> {
                    match (self, other) {
                        (Some(t), Some(u)) => Some((t, u)),
                        _ => None,
                    }
                }
            }

            impl<T, U> Option<(T, U)> {
                #[check(ghost)]
                #[ensures(match self {
                    None => result == (None, None),
                    Some((t, u)) => result == (Some(t), Some(u)),
                })]
                fn unzip(self) -> (Option<T>, Option<U>) {
                    match self {
                        Some((t, u)) => (Some(t), Some(u)),
                        None => (None, None),
                    }
                }
            }

            impl<T> Option<&T> {
                #[check(ghost)]
                #[ensures(match self {
                    None => result == None,
                    Some(s) => result == Some(*s)
                })]
                fn copied(self) -> Option<T>
                where
                    T: Copy {
                    match self {
                        None => None,
                        Some(t) => Some(*t),
                    }
                }

                #[ensures(match (self, result) {
                    (None, None) => true,
                    (Some(s), Some(r)) =>T::clone.postcondition((s,), r),
                    _ => false
                })]
                fn cloned(self) -> Option<T>
                where
                    T: Clone {
                    match self {
                        None => None,
                        Some(t) => Some(t.clone()),
                    }
                }
            }

            impl<T> Option<&mut T> {
                #[check(ghost)]
                #[ensures(match self {
                    None => result == None,
                    Some(s) => result == Some(*s) && ^s == *s
                })]
                fn copied(self) -> Option<T>
                where
                    T: Copy {
                    match self {
                        None => None,
                        Some(t) => Some(*t),
                    }
                }

                #[ensures(match (self, result) {
                    (None, None) => true,
                    (Some(s), Some(r)) => T::clone.postcondition((s,), r) && ^s == *s,
                    _ => false
                })]
                fn cloned(self) -> Option<T>
                where
                    T: Clone {
                    match self {
                        None => None,
                        Some(t) => Some(t.clone()),
                    }
                }
            }

            impl<T, E> Option<Result<T, E>> {
                #[check(ghost)]
                #[ensures(match self {
                    None => result == Ok(None),
                    Some(Ok(ok)) => result == Ok(Some(ok)),
                    Some(Err(err)) => result == Err(err),
                })]
                fn transpose(self) -> Result<Option<T>, E> {
                    match self {
                        None => Ok(None),
                        Some(Ok(ok)) => Ok(Some(ok)),
                        Some(Err(err)) => Err(err),
                    }
                }
            }

            impl<T> Option<Option<T>> {
                #[check(ghost)]
                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || self == Some(result))]
                fn flatten(self) -> Option<T> {
                    match self {
                        None => None,
                        Some(opt) => opt,
                    }
                }
            }
        }
    }

    impl<T> IntoIterator for Option<T>{
        #[check(ghost)]
        #[ensures(self == result@)]
        fn into_iter(self) -> IntoIter<T>;
    }

    impl<'a, T> IntoIterator for &'a Option<T>{
        #[check(ghost)]
        #[ensures(*self == match result@ { None => None, Some(r) => Some(*r) })]
        fn into_iter(self) -> Iter<'a, T>;
    }

    impl<'a, T> IntoIterator for &'a mut Option<T>{
        #[check(ghost)]
        #[ensures(*self == match result@ { None => None, Some(r) => Some(*r) })]
        #[ensures(^self == match result@ { None => None, Some(r) => Some(^r) })]
        fn into_iter(self) -> IterMut<'a, T>;
    }

    impl<T> Default for Option<T> {
        #[check(ghost)]
        #[ensures(result == None)]
        fn default() -> Option<T>;
    }
}

impl<T: OrdLogic> OrdLogic for Option<T> {
    #[logic(open)]
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

    #[logic(opaque)]
    fn view(self) -> Option<T> {
        dead
    }
}

impl<T> Iterator for IntoIter<T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> View for Iter<'a, T> {
    type ViewTy = Option<&'a T>;

    #[logic(opaque)]
    fn view(self) -> Option<&'a T> {
        dead
    }
}

impl<T> Iterator for Iter<'_, T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> View for IterMut<'a, T> {
    type ViewTy = Option<&'a mut T>;

    #[logic(opaque)]
    fn view(self) -> Option<&'a mut T> {
        dead
    }
}

impl<T> Iterator for IterMut<'_, T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

pub trait OptionExt<T> {
    /// Same as [`Option::unwrap`], but in logic.
    #[logic]
    #[requires(false)]
    fn unwrap_logic(self) -> T;

    /// Same as [`Option::and_then`], but in logic.
    #[logic]
    fn and_then_logic<U>(self, f: Mapping<T, Option<U>>) -> Option<U>;

    /// Same as [`Option::map`], but in logic.
    #[logic]
    fn map_logic<U>(self, f: Mapping<T, U>) -> Option<U>;
}

impl<T> OptionExt<T> for Option<T> {
    #[logic(open)]
    #[requires(self != None)]
    fn unwrap_logic(self) -> T {
        match self {
            Some(x) => x,
            None => such_that(|_| true),
        }
    }

    #[logic(open)]
    fn and_then_logic<U>(self, f: Mapping<T, Option<U>>) -> Option<U> {
        match self {
            None => None,
            Some(x) => f.get(x),
        }
    }

    #[logic(open)]
    fn map_logic<U>(self, f: Mapping<T, U>) -> Option<U> {
        match self {
            None => None,
            Some(x) => Some(f.get(x)),
        }
    }
}

impl<T> Resolve for Option<T> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        match self {
            Some(x) => resolve(x),
            None => true,
        }
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}
