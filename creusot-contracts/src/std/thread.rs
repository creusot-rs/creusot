use crate::{ghost::local_invariant::Tokens, prelude::*};
use ::std::thread::JoinHandle;

/// Extension trait for [`JoinHandle`].
pub trait JoinHandleExt<T> {
    /// Predicate that specifies the valid return results for the handle.
    #[logic]
    fn valid_result(self, x: T) -> bool;
}

impl<T> JoinHandleExt<T> for JoinHandle<T> {
    #[logic(opaque)]
    fn valid_result(self, _x: T) -> bool {
        dead
    }
}

extern_spec! {
    mod std {
        mod thread {
            impl<T> JoinHandle<T> {
                #[ensures(match result {
                    Ok(res) => self.valid_result(res),
                    Err(_) => true,
                })]
                fn join(self) -> ::std::thread::Result<T>;

                #[ensures(true)] // no spec, but you can call this if you want
                fn is_finished(&self) -> bool;
            }
        }
    }
}

/// Creusot wrapper around [`std::thread::spawn`].
///
/// The only difference is that the closure gives access to a fresh
#[requires(forall<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) ==> f.precondition((t,)))]
#[ensures(exists<t: Ghost<Tokens>> (forall<ns> t.contains(ns)) ==> forall<r> result.valid_result(r) ==> f.postcondition_once((t,), r))]
#[trusted]
pub fn spawn<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce(Ghost<Tokens>) -> T + Send + 'static,
    T: Send + 'static,
{
    ::std::thread::spawn(|| f(Tokens::new()))
}
