use crate::{ghost::invariant::Tokens, prelude::*};
use ::std::thread::{self, JoinHandle, ScopedJoinHandle};

/// Extension trait for [`JoinHandle`].
pub trait JoinHandleExt<T> {
    /// Predicate that specifies the valid return results for the handle.
    #[logic(prophetic)]
    fn valid_result(self, x: T) -> bool;

    /// This function is a wrapper `self.join().unwrap()`.
    ///
    /// This function panics only on stack-overflow or OOM on the spawned thread.
    // NOTE: This is a way to avoid ::std::thread::Result, which:
    //  - contains a dyn;
    //  - we don't know how to handle the Err case in Creusot.
    #[ensures(self.valid_result(result))]
    fn join_unwrap(self) -> T;
}

impl<T> JoinHandleExt<T> for JoinHandle<T> {
    #[logic(opaque, prophetic)]
    fn valid_result(self, _x: T) -> bool {
        dead
    }

    #[ensures(self.valid_result(result))]
    #[trusted]
    fn join_unwrap(self) -> T {
        self.join().unwrap()
    }
}

impl<T> JoinHandleExt<T> for ScopedJoinHandle<'_, T> {
    #[logic(opaque, prophetic)]
    fn valid_result(self, _x: T) -> bool {
        dead
    }

    #[ensures(self.valid_result(result))]
    #[trusted]
    fn join_unwrap(self) -> T {
        self.join().unwrap()
    }
}

extern_spec! {
    impl<T> JoinHandle<T> {
        #[ensures(true)] // no spec, but you can call this if you want
        fn is_finished(&self) -> bool;
    }

    impl<T> ScopedJoinHandle<'_, T> {
        #[ensures(true)] // no spec, but you can call this if you want
        fn is_finished(&self) -> bool;
    }
}

/// Creusot wrapper around [`std::thread::spawn`].
///
/// The only difference is that the closure gives access to a fresh token object
#[requires(|mode| forall<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) ==> f.precondition(mode, (t,)))]
#[ensures(|result, mode| exists<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) && forall<r> result.valid_result(r) ==> f.postcondition_once(mode, (t,), r))]
#[trusted]
pub fn spawn<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce(Ghost<Tokens>) -> T + Send + 'static,
    T: Send + 'static,
{
    ::std::thread::spawn(|| f(Tokens::new()))
}

/// Creusot's replacement for [`Scope`].
pub struct Scope<'scope, 'env: 'scope> {
    inner: &'scope thread::Scope<'scope, 'env>,
}

impl<'scope, 'env: 'scope> Scope<'scope, 'env> {
    #[requires(|mode| forall<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) ==> f.precondition(mode, (t,)))]
    #[ensures(|result, mode| exists<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) && forall<r> result.valid_result(r) ==> f.postcondition_once(mode, (t,), r))]
    #[trusted]
    pub fn spawn<F, T>(&mut self, f: F) -> ScopedJoinHandle<'scope, T>
    where
        F: FnOnce(Ghost<Tokens>) -> T + Send + 'scope,
        T: Send + 'scope,
    {
        self.inner.spawn(|| f(Tokens::new()))
    }
}

/// Creusot wrapper around [`std::thread::scope`].
#[requires(|mode| forall<s> inv(s) ==> f.precondition(mode, (s,)))]
#[ensures(|result, mode| exists<s> inv(s) && f.postcondition_once(mode, (s,), result))]
#[trusted]
pub fn scope<'env, F, T>(f: F) -> T
where
    F: for<'scope> FnOnce(&mut Scope<'scope, 'env>) -> T,
{
    ::std::thread::scope(|s| f(&mut Scope { inner: s }))
}
