use crate as creusot_contracts;
use crate::std::{default::DefaultSpec, fun::FnOnceSpec};
use creusot_contracts_proc::*;

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

                #[ensures(result == match self {
                    Some(inner) => inner,
                    None => default,
                })]
                fn unwrap_or(self, default: T) -> T;

                #[requires(self != None || f.precondition(()))]
                #[ensures(match self {
                    Some(inner) => result == inner,
                    None => f.postcondition_once((), result),
                })]
                fn unwrap_or_else<F>(self, f: F) -> T
                where
                    F: FnOnce() -> T;

                #[ensures(*self == None ==> result == None && ^self == None)]
                #[ensures(
                    *self == None
                    || exists<r: &mut T> result == Some(r) && *self == Some(*r) && ^self == Some(^r)
                )]
                fn as_mut(&mut self) -> Option<&mut T>;

                #[ensures(*self == None ==> result == None)]
                #[ensures(
                    *self == None || exists<r: &mut T> result == Some(r) && *self == Some(*r)
                )]
                fn as_ref(&self) -> Option<&T>;

                #[ensures(result == match self {
                    Some(inner) => Ok(inner),
                    None => Err(err),
                })]
                fn ok_or<E>(self, err: E) -> Result<T, E>;

                #[requires(self != None || err.precondition(()))]
                #[ensures(match self {
                    Some(inner) => result == Ok(inner),
                    None => exists<e: E> err.postcondition_once((), e) && result == Err(e),
                })]
                fn ok_or_else<E, F>(self, err: F) -> Result<T, E>
                where
                    F: FnOnce() -> E;

                #[requires(match self {
                    Some(inner) => f.precondition((inner,)),
                    None => true,
                })]
                #[ensures(match self {
                    Some(inner) =>
                        exists<r: U> f.postcondition_once((inner,), r) && result == Some(r),
                    None => result == None,
                })]
                fn map<U, F>(self, f: F) -> Option<U>
                where
                    F: FnOnce(T) -> U;

                #[requires(match self {
                    Some(inner) => f.precondition((inner,)),
                    None => true,
                })]
                #[ensures(match self {
                    Some(inner) => f.postcondition_once((inner,), result),
                    None => result == default,
                })]
                fn map_or<U, F>(self, default: U, f: F) -> U
                where
                    F: FnOnce(T) -> U;

                #[requires(match self {
                    Some(inner) => f.precondition((inner,)),
                    None => default.precondition(()),
                })]
                #[ensures(match self {
                    Some(inner) => f.postcondition_once((inner,), result),
                    None => default.postcondition_once((), result),
                })]
                fn map_or_else<U, D, F>(self, default: D, f: F) -> U
                where
                    D: FnOnce() -> U,
                    F: FnOnce(T) -> U;

                #[ensures(result == match self {
                    Some(_) => optb,
                    None => None,
                })]
                fn and<U>(self, optb: Option<U>) -> Option<U>;

                #[requires(match self {
                    Some(inner) => f.precondition((inner,)),
                    None => true,
                })]
                #[ensures(match self {
                    Some(inner) => f.postcondition_once((inner,), result),
                    None => result == None,
                })]
                fn and_then<U, F>(self, f: F) -> Option<U>
                where
                    F: FnOnce(T) -> Option<U>;

                #[ensures(result == match self {
                    Some(_) => self,
                    None => optb,
                })]
                fn or(self, optb: Option<T>) -> Option<T>;

                #[requires(match self {
                    Some(_) => true,
                    None => f.precondition(()),
                })]
                #[ensures(match self {
                    Some(_) => result == self,
                    None => f.postcondition_once((), result),
                })]
                fn or_else<F>(self, f: F) -> Option<T>
                where
                    F: FnOnce() -> Option<T>;

                #[requires(
                    self == None || exists<r: &T> self == Some(*r) && predicate.precondition((r,))
                )]
                #[ensures(match self {
                    Some(t) => exists<r: &T> *r == t && (
                        (predicate.postcondition_once((r,), false) && result == None)
                        || (predicate.postcondition_once((r,), true) && result == self)
                    ),
                    None => result == None,
                })]
                fn filter<P>(self, predicate: P) -> Option<T>
                where
                    P: FnOnce(&T) -> bool;

                #[ensures(result == *self && ^self == None)]
                fn take(&mut self) -> Option<T>;

                #[ensures(result == *self && ^self == Some(value))]
                fn replace(&mut self, value: T) -> Option<T>;

                #[ensures(result == match self {
                    Some(inner) => inner,
                    None => T::default_log(),
                })]
                fn unwrap_or_default(self) -> T
                where
                    T: DefaultSpec;
            }

            impl<T> Option<&T> {
                #[ensures(result == match self {
                    Some(t) => Some(*t),
                    None => None,
                })]
                fn copied(self) -> Option<T>
                where
                    T: Copy;

                #[ensures(result == match self {
                    Some(t) => Some(*t),
                    None => None,
                })]
                fn cloned(self) -> Option<T>
                where
                    T: Clone;
            }

            impl<T> Option<&mut T> {
                #[ensures(result == match self {
                    Some(t) => Some(*t),
                    None => None,
                })]
                fn copied(self) -> Option<T>
                where
                    T: Copy;

                #[ensures(result == match self {
                    Some(t) => Some(*t),
                    None => None,
                })]
                fn cloned(self) -> Option<T>
                where
                    T: Clone;
            }

            impl<T> Option<Option<T>> {
                #[ensures(result == match self {
                    Some(inner) => inner,
                    None => None,
                })]
                fn flatten(self) -> Option<T>;
            }
        }
    }
}

impl<T> DefaultSpec for Option<T> {
    #[logic]
    fn default_log() -> Option<T> {
        None
    }
}
