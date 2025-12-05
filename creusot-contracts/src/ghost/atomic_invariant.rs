//! Define atomic invariants.
//!
//! Atomic invariants are used to specify concurrent operations.

use crate::{ghost::FnGhost, prelude::*};

/// Creusot wrapper around [`std::sync::atomic::AtomicI32`]
pub struct AtomicI32(::std::sync::atomic::AtomicI32);

/// Does a single atomic operation, in ghost
#[opaque]
pub struct Committer;

/// Ownership for a [`AtomicI32`].
#[opaque]
pub struct AtomicI32Own;

impl AtomicI32Own {
    /// Which atomic does this holds the ownership for
    #[logic(opaque)]
    pub fn id(self) -> AtomicI32 {
        dead
    }

    /// Value currently contained in the atomic
    #[logic(opaque)]
    pub fn val(self) -> i32 {
        dead
    }
}

impl Committer {
    /// Status of the committer
    #[logic(opaque)]
    pub fn shot(self) -> bool {
        dead
    }

    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn id(self) -> AtomicI32 {
        dead
    }

    /// Value that will be written to the [`AtomicOwn`]
    #[logic(opaque)]
    pub fn final_value(self) -> i32 {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!self.shot())]
    #[requires(self.id() == own.id())]
    #[ensures((^self).shot())]
    #[ensures((^own).id() == (*own).id())]
    #[ensures((^own).val() == self.final_value())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut AtomicI32Own) {
        panic!("Should not be called outside ghost code")
    }
}

impl AtomicI32 {
    /// Wrapper for [`std::sync::atomic::AtomicI32::store`].
    ///
    /// The store is always sequentially consistent.
    #[requires(forall<c: &mut Committer> !c.shot() ==> c.id() == *self ==> c.final_value() == val ==>
        f.precondition((c,)) &&
        (forall<r> f.postcondition_once((c,), r) ==> (^c).shot())
    )]
    #[ensures(exists<c: &mut Committer>
        !c.shot() && c.id() == *self && c.final_value() == val &&
        f.postcondition_once((c,), *result)
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn store<A, F>(&self, val: i32, f: Ghost<F>) -> Ghost<A>
    where
        F: FnGhost + FnOnce(&mut Committer) -> A,
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
        Ghost::conjure()
    }
}
