use creusot_std::{
    ghost::FnGhost,
    prelude::*,
    std::sync::{atomic::Ordering, atomic_sc::AtomicI32, committer::Committer},
};

#[requires(forall<c: &mut Committer<AtomicI32, i32, Ordering::SeqCst, Ordering::SeqCst>>
    !c.shot_store() ==> c.ward() == *at ==> c.val_store() == val + c.val_load() ==>
    f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot_store())
)]
#[ensures(exists<c: &mut Committer<AtomicI32, i32, Ordering::SeqCst, Ordering::SeqCst>>
    !c.shot_store() && c.ward() == *at && c.val_store() == val + c.val_load() &&
    c.val_load() == result && f.postcondition_once((c,), ())
)]
pub fn fetch_add<F>(at: &AtomicI32, val: i32, f: Ghost<F>) -> i32
where
    // Interestingly, we do not need to have an "abort" case in the atomic update like in Iris or
    // Verus. The reason is that we do not need the permission to the atomic variable when then
    // compare_exchange operation fails.
    F: FnGhost + FnOnce(&mut Committer<AtomicI32, i32, Ordering::SeqCst, Ordering::SeqCst>),
{
    let mut old = at.load(ghost!(|_: &_| {}));
    let old_f = snapshot!(f);
    let mut f = ghost!(Some(f.into_inner()));

    #[invariant(*f == Some(**old_f))]
    while let Err(o) = at.compare_exchange_weak(
        old,
        old.wrapping_add(val),
        ghost!(|c: Result<
            &mut Committer<AtomicI32, i32, Ordering::SeqCst, Ordering::SeqCst>,
            &_,
        >| {
            if let Ok(c) = c {
                f.take().unwrap()(c)
            }
        }),
    ) {
        old = o
    }
    old
}
