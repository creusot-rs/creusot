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
        // We give no spec to this function, because it can return `true` if the thread has panicked.
        // But you can call this if you want.
        #[ensures(true)]
        fn is_finished(&self) -> bool;
    }

    impl<T> ScopedJoinHandle<'_, T> {
        // We give no spec to this function, because it can return `true` if the thread has panicked.
        // But you can call this if you want.
        #[ensures(true)]
        fn is_finished(&self) -> bool;

        #[ensures(exists<r> result == Ok(r) && self.valid_result(r))]
        fn join(self) -> ::std::thread::Result<T>;
    }
}

/// Creusot wrapper around [`std::thread::spawn`].
///
/// The only difference is that the closure gives access to a fresh token object
#[requires(forall<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) ==> f.precondition((t,)))]
#[ensures(exists<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) && forall<r> result.valid_result(r) ==> f.postcondition_once((t,), r))]
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
    #[requires(forall<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) ==> f.precondition((t,)))]
    #[ensures(exists<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) && forall<r> result.valid_result(r) ==> f.postcondition_once((t,), r))]
    #[trusted]
    #[erasure(std::thread::Scope::spawn::<ErasedScope<F, T>, T>)]
    pub fn spawn<F, T>(&self, f: F) -> ScopedJoinHandle<'scope, T>
    where
        F: FnOnce(Ghost<Tokens>) -> T + Send + 'scope,
        T: Send + 'scope,
    {
        self.inner.spawn(|| f(Tokens::new()))
    }
}

/// Creusot wrapper around [`std::thread::scope`].
#[requires(forall<s> inv(s) ==> f.precondition((s,)))]
#[ensures(exists<s> inv(s) && f.postcondition_once((s,),result))]
#[trusted]
#[erasure(std::thread::scope::<'env, ErasedScope<'env, F, T>,T>)]
pub fn scope<'env, F, T>(f: F) -> T
where
    F: for<'scope> FnOnce(&Scope<'scope, 'env>) -> T,
{
    ::std::thread::scope(|s| f(&Scope { inner: s }))
}

#[cfg(creusot)]
pub struct ErasedScope<'env, F, T>(std::marker::PhantomData<(&'env (), F, T)>);

#[cfg(creusot)]
#[trusted]
unsafe impl<F: Send, T> Send for ErasedScope<'_, F, T> {}

#[cfg(creusot)]
impl<'scope, 'env, 'a, F: for<'scope2> FnOnce(&Scope<'scope2, 'env>) -> T, T>
    FnOnce<(&'scope ::std::thread::Scope<'scope, 'a>,)> for ErasedScope<'env, F, T>
{
    type Output = T;
    #[trusted]
    extern "rust-call" fn call_once(self, args: (&'scope ::std::thread::Scope,)) -> T {
        todo!() // self.0(args.0)
    }
}

#[cfg(creusot)]
impl<'scope, F: FnOnce(Ghost<Tokens>) -> T + 'scope, T> FnOnce<()> for ErasedScope<'_, F, T> {
    type Output = T;

    #[trusted]
    extern "rust-call" fn call_once(self, args: ()) -> T {
        todo!() // self.0(args.0)
    }
}
