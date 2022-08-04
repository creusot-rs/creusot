use crate as creusot_contracts;
use crate::{
    std::{default::DefaultSpec, fun::FnOnceSpec},
    Resolve,
};
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

                #[ensures(self == None ==> result == default)]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or(self, default: T) -> T;

                #[requires(self != None || f.precondition(()))]
                #[ensures(self == None ==> f.postcondition_once((), result))]
                #[ensures(self == None || self == Some(result))]
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
                    *self == None || exists<r: &T> result == Some(r) && *self == Some(*r)
                )]
                fn as_ref(&self) -> Option<&T>;

                #[ensures(self == None ==> result == Err(err))]
                #[ensures(self == None || exists<t: T> self == Some(t) && result == Ok(t))]
                fn ok_or<E>(self, err: E) -> Result<T, E>;

                #[requires(self != None || err.precondition(()))]
                #[ensures(
                    self == None ==> exists<e: E> err.postcondition_once((), e) && result == Err(e)
                )]
                #[ensures(self == None || exists<t: T> self == Some(t) && result == Ok(t))]
                fn ok_or_else<E, F>(self, err: F) -> Result<T, E>
                where
                    F: FnOnce() -> E;

                #[requires(self == None || exists<t: T> self == Some(t) && f.precondition((t,)))]
                #[ensures(self == None ==> result == None)]
                #[ensures(
                    self == None
                    || exists<t: T, u: U> self == Some(t) && result == Some(u)
                        && f.postcondition_once((t,), u)
                )]
                fn map<U, F>(self, f: F) -> Option<U>
                where
                    F: FnOnce(T) -> U;

                #[requires(self == None || exists<t: T> self == Some(t) && f.precondition((t,)))]
                #[ensures(self == None ==> result == default)]
                #[ensures(
                    self == None
                    || exists<t: T, u: U> self == Some(t) && result == u
                        && f.postcondition_once((t,), u)
                )]
                fn map_or<U, F>(self, default: U, f: F) -> U
                where
                    F: FnOnce(T) -> U;

                #[requires(
                    (self == None && default.precondition(()))
                    || exists<t: T> self == Some(t) && f.precondition((t,))
                )]
                #[ensures(self == None ==> default.postcondition_once((), result))]
                #[ensures(
                    self == None
                    || exists<t: T, u: U> self == Some(t) && result == u
                        && f.postcondition_once((t,), u)
                )]
                fn map_or_else<U, D, F>(self, default: D, f: F) -> U
                where
                    D: FnOnce() -> U,
                    F: FnOnce(T) -> U;

                #[ensures(self == None ==> result == None)]
                #[ensures(self == None || result == optb)]
                fn and<U>(self, optb: Option<U>) -> Option<U>;

                #[requires(self == None || exists<t: T> self == Some(t) && f.precondition((t,)))]
                #[ensures(self == None ==> result == None)]
                #[ensures(
                    self == None
                    || exists<t: T> self == Some(t) && f.postcondition_once((t,), result)
                )]
                fn and_then<U, F>(self, f: F) -> Option<U>
                where
                    F: FnOnce(T) -> Option<U>;

                #[ensures(self == None ==> result == optb)]
                #[ensures(self == None || result == self)]
                fn or(self, optb: Option<T>) -> Option<T>;

                #[requires(self != None || f.precondition(()))]
                #[ensures(self == None ==> f.postcondition_once((), result))]
                #[ensures(self == None || result == self)]
                fn or_else<F>(self, f: F) -> Option<T>
                where
                    F: FnOnce() -> Option<T>;

                #[requires(
                    self == None || exists<r: &T> self == Some(*r) && predicate.precondition((r,))
                )]
                #[ensures(self == None ==> result == None)]
                #[ensures(
                    self == None
                    || exists<r: &T> self == Some(*r) && (
                        (predicate.postcondition_once((r,), false) && result == None)
                        || (predicate.postcondition_once((r,), true) && result == self)
                    )
                )]
                fn filter<P>(self, predicate: P) -> Option<T>
                where
                    P: FnOnce(&T) -> bool;

                #[ensures(result == *self && ^self == None)]
                fn take(&mut self) -> Option<T>;

                #[ensures(result == *self && ^self == Some(value))]
                fn replace(&mut self, value: T) -> Option<T>;

                #[ensures(self == None ==> result == T::default_log())]
                #[ensures(self == None || self == Some(result))]
                fn unwrap_or_default(self) -> T
                where
                    T: DefaultSpec;
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

impl<T> DefaultSpec for Option<T> {
    #[logic]
    fn default_log() -> Option<T> {
        None
    }
}
