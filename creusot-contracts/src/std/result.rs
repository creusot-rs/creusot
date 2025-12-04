use crate::prelude::*;
use core::fmt::Debug;

impl<T: DeepModel, E: DeepModel> DeepModel for Result<T, E> {
    type DeepModelTy = Result<T::DeepModelTy, E::DeepModelTy>;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Ok(t) => Ok(t.deep_model()),
            Err(e) => Err(e.deep_model()),
        }
    }
}

extern_spec! {
    mod std {
        mod result {
            impl<T, E> Result<T, E> {
                #[check(ghost)]
                #[ensures(result == exists<t: T> *self == Ok(t))]
                fn is_ok(&self) -> bool;

                #[check(ghost)]
                #[ensures(result == exists<e: E> *self == Err(e))]
                fn is_err(&self) -> bool;

                #[check(ghost)]
                #[ensures(forall<t: T> self == Ok(t) ==> result == Some(t))]
                #[ensures((exists<e: E> self == Err(e)) ==> result == None)]
                fn ok(self) -> Option<T>;

                #[check(ghost)]
                #[ensures((exists<t: T> self == Ok(t)) ==> result == None)]
                #[ensures(forall<e: E> self == Err(e) ==> result == Some(e))]
                fn err(self) -> Option<E>;

                #[check(ghost)]
                #[ensures(forall<t: &T> *self == Ok(*t) ==> result == Ok(t))]
                #[ensures(forall<e: &E> *self == Err(*e) ==> result == Err(e))]
                fn as_ref(&self) -> Result<&T, &E>;

                #[check(ghost)]
                #[ensures(
                    exists<t: &mut T> *self == Ok(*t) && ^self == Ok(^t) && result == Ok(t) ||
                    exists<e: &mut E> *self == Err(*e) && ^self == Err(^e) && result == Err(e)
                )]
                fn as_mut(&mut self) -> Result<&mut T, &mut E>;

                #[check(ghost)]
                #[requires(exists<t: T> self == Ok(t))]
                #[ensures(Ok(result) == self)]
                fn unwrap(self) -> T
                where
                    E: Debug;

                #[check(ghost)]
                #[requires(exists<t: T> self == Ok(t))]
                #[ensures(Ok(result) == self)]
                fn expect(self, msg: &str) -> T
                where
                    E: Debug;

                #[check(ghost)]
                #[requires(exists<e: E> self == Err(e))]
                #[ensures(Err(result) == self)]
                fn unwrap_err(self) -> E
                where
                    T: Debug;

                #[check(ghost)]
                #[ensures(forall<t: T> self == Ok(t) ==> result == t)]
                #[ensures((exists<e: E> self == Err(e)) ==> result == default)]
                fn unwrap_or(self, default: T) -> T;

                #[ensures(forall<t: T> self == Ok(t) ==> result == t)]
                #[ensures((exists<e: E> self == Err(e)) ==> T::default.postcondition((), result))]
                fn unwrap_or_default(self) -> T
                where
                    T: Default;

                #[check(ghost)]
                #[ensures((exists<t: T> self == Ok(t)) ==> result == res)]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn and<U>(self, res: Result<U, E>) -> Result<U, E>;

                #[check(ghost)]
                #[ensures(forall<t: T> self == Ok(t) ==> result == Ok(t))]
                #[ensures((exists<e: E> self == Err(e)) ==> result == res)]
                fn or<F>(self, res: Result<T, F>) -> Result<T, F>;
            }

            impl<T, E> Result<&T, E> {
                #[check(ghost)]
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
                #[check(ghost)]
                #[ensures(forall<t: &mut T> self == Ok(t) ==> result == Ok(*t) && resolve(t))]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn copied(self) -> Result<T, E>
                where
                    T: Copy;

                #[ensures(forall<t: &mut T> self == Ok(t) ==> result == Ok(*t) && resolve(t))]
                #[ensures(forall<e: E> self == Err(e) ==> result == Err(e))]
                fn cloned(self) -> Result<T, E>
                where
                    T: Clone;
            }

            impl<T, E> Result<Option<T>, E> {
                #[check(ghost)]
                #[ensures(self == Ok(None) ==> result == None)]
                #[ensures(forall<t: T> self == Ok(Some(t)) ==> result == Some(Ok(t)))]
                #[ensures(forall<e: E> self == Err(e) ==> result == Some(Err(e)))]
                fn transpose(self) -> Option<Result<T, E>>;
            }
        }
    }
}
