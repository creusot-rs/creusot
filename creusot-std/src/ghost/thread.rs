//! Ghost tokens to reason about the number of threads.
//!
//! If you are looking to prove a concurrent algorithm, you might be more
//! interested in [atomic invariants](crate::ghost::invariant::AtomicInvariant).

use crate::{
    ghost::invariant::{Tokens, declare_namespace},
    invariant::Guarded,
    prelude::*,
};

declare_namespace! { THREAD_TOKEN }

/// Maximal number of threads that can be running simultaneously.
pub const MAX_LIVE_THREADS: usize = usize::MAX / 2;

/// A special token asserting the liveness of a given thread.
///
/// You can create one by giving up a [`Tokens`] containing the [`THREAD_TOKEN`]
/// namespace.
///
/// For now, it has only one special property: it can be used to express
/// that the number of threads is bounded, in particular it is less than
/// [`MAX_LIVE_THREADS`]. This might also be used in the future to carry thread
/// ids.
#[opaque]
#[allow(dead_code)]
pub struct ThreadToken(());

impl ThreadToken {
    /// Get a temporary thread token, that asserts that the current thread is
    /// still alive.
    ///
    /// To ensure that there is only one such token per thread, you need to
    /// temporarily give a `Tokens` object containing the [`THREAD_TOKEN`]
    /// namespace.
    #[trusted]
    #[requires(tokens.contains(THREAD_TOKEN()))]
    #[ensures(result.guard() == |tt: &mut Option<Self>| *tt != None)]
    #[check(ghost)]
    pub fn get_thread_token<'a>(
        #[allow(unused)] tokens: Tokens<'a>,
    ) -> Guarded<&'a mut Option<Self>> {
        panic!("ghost only")
    }

    /// Ghost lemma, to bound the total number of threads.
    ///
    /// We are certain that it is impossible to spawn more than [`MAX_LIVE_THREADS`]
    /// threads _at the same time_ ; and, each `ThreadToken` is associated to
    /// exactly one _live_ thread.
    #[check(ghost)]
    #[trusted]
    #[ensures(thread_tokens.len() < MAX_LIVE_THREADS@)]
    #[allow(unused_variables)]
    pub fn bound_thread_number(thread_tokens: &Seq<Self>) {}
}
