use crate::{
    ghost::{Container, perm::Perm},
    prelude::*,
};
use core::marker::PhantomData;

pub struct None;
pub struct Relaxed;
pub struct Release;
pub struct Acquire;
pub struct SeqCst;

/// Wrapper around a single atomic operation, where multiple ghost steps can be performed.
///
/// Note: this committer has no observable effect on ghost ressources. Thus, it is optional to shoot
/// it, and nothing prevent the user from shooting it several times.
// This trick is correct for SC accesses under SC-DRF, and for Rel/Acq/Rlx and Rlx accesses, but
// perhaps not for C20's SC accesses.
#[opaque]
pub struct Committer<C: Container<Value: Sized>, LoadAccess, StoreAccess>(
    PhantomData<(C, LoadAccess, StoreAccess)>,
);

impl<C: Container<Value: Sized>, LoadAccess, StoreAccess> Committer<C, LoadAccess, StoreAccess> {
    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn ward(self) -> C {
        dead
    }

    /// Value read from the atomic operation.
    #[logic(opaque)]
    pub fn val_load(self) -> C::Value {
        dead
    }

    /// Value written by the atomic operation.
    #[logic(opaque)]
    pub fn val_store(self) -> C::Value {
        dead
    }

    #[logic(open, inline)]
    pub fn hist_inv(self, other: Self) -> bool {
        self.ward() == other.ward()
            && self.val_load() == other.val_load()
            && self.val_store() == other.val_store()
    }
}

impl<C: Container<Value: Sized>, StoreAccess> Committer<C, SeqCst, StoreAccess> {
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code, and can only be called once.
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(self.val_load() == *own.val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}

impl<C: Container<Value: Sized>, LoadAccess> Committer<C, LoadAccess, SeqCst> {
    /// Status of the committer
    #[logic(opaque)]
    pub fn shot_store(self) -> bool {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((^self).shot_store())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures((*self).val_store() == *(^own).val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}
