use crate as creusot_contracts;
use crate::{
    std::{default::DefaultSpec, fun::FnOnceSpec},
    Resolve,
};
use creusot_contracts_proc::*;
use std::fmt::Debug;

extern_spec! {
    mod std {
        mod result {
            impl<T, E> Result<T, E> {
                #[ensures(result == exists<t: T> *self == Ok(t))]
                fn is_ok(&self) -> bool;

                #[ensures(result == exists<e: E> *self == Err(e))]
                fn is_err(&self) -> bool;

                #[ensures(forall<t: T> self == Ok(t) ==> result == Some(t))]
                #[ensures((exists<e: E> self == Err(e)) ==> result == None)]
                fn ok(self) -> Option<T>;

                #[ensures((exists<t: T> self == Ok(t)) ==> result == None)]
                #[ensures(forall<e: E> self == Err(e) ==> result == Some(e))]
                fn err(self) -> Option<E>;

                #[ensures(forall<t: &T> *self == Ok(*t) ==> result == Ok(t))]
                #[ensures(forall<e: &E> *self == Err(*e) ==> result == Err(e))]
                #[ensures((exists<t: &T> *self == Ok(*t))|| (exists<e: &E> *self == Err(*e)))]
                fn as_ref(&self) -> Result<&T, &E>;

                #[ensures(
                    forall<t: &mut T> *self == Ok(*t) ==> ^self == Ok(^t) && result == Ok(t)
                )]
                #[ensures(
                    forall<e: &mut E> *self == Err(*e) ==> ^self == Err(^e) && result == Err(e)
                )]
                #[ensures(
                    (exists<t: &mut T> *self == Ok(*t))|| (exists<e: &mut E> *self == Err(*e))
                )]
                fn as_mut(&mut self) -> Result<&mut T, &mut E>;

                #[requires(exists<t: T> self == Ok(t))]
                #[ensures(Ok(result) == self)]
                fn unwrap(self) -> T
                where
                    E: Debug;

                #[requires(exists<t: T> self == Ok(t))]
                #[ensures(Ok(result) == self)]
                fn expect(self, msg: &str) -> T
                where
                    E: Debug;

                #[requires(exists<e: E> self == Err(e))]
                #[ensures(Err(result) == self)]
                fn unwrap_err(self) -> E
                where
                    T: Debug;

                #[ensures(forall<t: T> self == Ok(t) ==> result == t)]
                #[ensures((exists<e: E> self == Err(e)) ==> result == default)]
                fn unwrap_or(self, default: T) -> T;

                #[ensures(forall<t: T> self == Ok(t) ==> result == t)]
                #[ensures((exists<e: E> self == Err(e)) ==> result == T::default_log())]
                fn unwrap_or_default(self) -> T
                where
                    T: DefaultSpec;

                #[requires(forall<e: E> self == Err(e) ==> op.precondition((e,)))]
                #[ensures(forall<t: T> self == Ok(t) ==> result == t)]
                #[ensures(forall<e: E> self == Err(e) ==> op.postcondition_once((e,), result))]
                fn unwrap_or_else<F>(self, op: F) -> T
                where
                    F: FnOnce(E) -> T;

                #[requires(forall<t: T> self == Ok(t) ==> op.precondition((t,)))]
                #[ensures(
                    forall<t: T> self == Ok(t)
                    ==> exists<u: U> op.postcondition_once((t,), u) && result == Ok(u)
                )]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn map<U, F>(self, op: F) -> Result<U, E>
                where
                    F: FnOnce(T) -> U;

                #[requires(forall<t: T> self == Ok(t) ==> op.precondition((t,)))]
                #[ensures(forall<t: T> self == Ok(t) ==> op.postcondition_once((t,), result))]
                #[ensures((exists<e: E> self == Err(e)) ==> result == default)]
                fn map_or<U, F>(self, default: U, op: F) -> U
                where
                    F: FnOnce(T) -> U;

                #[requires(forall<t: T> self == Ok(t) ==> op.precondition((t,)))]
                #[requires(forall<e: E> self == Err(e) ==> default.precondition((e,)))]
                #[ensures(forall<t: T> self == Ok(t) ==> op.postcondition_once((t,), result))]
                #[ensures(forall<e: E> self == Err(e) ==> default.postcondition_once((e,), result))]
                fn map_or_else<U, D, F>(self, default: D, op: F) -> U
                where
                    D: FnOnce(E) -> U,
                    F: FnOnce(T) -> U;

                #[requires(forall<e: E> self == Err(e) ==> op.precondition((e,)))]
                #[ensures(
                    forall<e: E> self == Err(e)
                    ==> exists<f: F> op.postcondition_once((e,), f) && result == Err(f)
                )]
                #[ensures(forall<t: T> self == Ok(t) ==> result == Ok(t))]
                fn map_err<F, O>(self, op: O) -> Result<T, F>
                where
                    O: FnOnce(E) -> F;

                #[ensures((exists<t: T> self == Ok(t)) ==> result == res)]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn and<U>(self, res: Result<U, E>) -> Result<U, E>;

                #[requires(forall<t: T> self == Ok(t) ==> op.precondition((t,)))]
                #[ensures(forall<t: T> self == Ok(t) ==> op.postcondition_once((t,), result))]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn and_then<U, F>(self, op: F) -> Result<U, E>
                where
                    F: FnOnce(T) -> Result<U, E>;

                #[ensures(forall<t: T> self == Ok(t) ==> result == Ok(t))]
                #[ensures((exists<e: E> self == Err(e)) ==> result == res)]
                fn or<F>(self, res: Result<T, F>) -> Result<T, F>;

                #[requires(forall<e: E> self == Err(e) ==> op.precondition((e,)))]
                #[ensures(forall<t: T> self == Ok(t) ==> result == Ok(t))]
                #[ensures(forall<e: E> self == Err(e) ==> op.postcondition_once((e,), result))]
                fn or_else<F, O>(self, op: O) -> Result<T, F>
                where
                    O: FnOnce(E) -> Result<T, F>;
            }

            impl<T, E> Result<&T, E> {
                #[ensures(forall<t: &T> self == Ok(t) ==> result == Ok(*t))]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn copied(self) -> Result<T, E>
                where
                    T: Copy;

                #[ensures(forall<t: &T> self == Ok(t) ==> result == Ok(*t))]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn cloned(self) -> Result<T, E>
                where
                    T: Clone;
            }

            impl<T, E> Result<&mut T, E> {
                #[ensures(forall<t: &mut T> self == Ok(t) ==> result == Ok(*t) && t.resolve())]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn copied(self) -> Result<T, E>
                where
                    T: Copy;

                #[ensures(forall<t: &mut T> self == Ok(t) ==> result == Ok(*t) && t.resolve())]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn cloned(self) -> Result<T, E>
                where
                    T: Clone;
            }

            impl<T, E> Result<Option<T>, E> {
                #[ensures(self == Ok(None) ==> result == None)]
                #[ensures(forall<t: T> self == Ok(Some(t)) ==> result == Some(Ok(t)))]
                #[ensures(forall<e: E> self == Err(e) ==> result == Some(Err(e)))]
                fn transpose(self) -> Option<Result<T, E>>;
            }
        }
    }
}
