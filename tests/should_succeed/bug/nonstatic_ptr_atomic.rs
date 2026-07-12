extern crate creusot_std;
use creusot_std::{
    ghost::perm::Perm,
    prelude::*,
    std::sync::{
        atomic::{AtomicPtr, ordering::Acquire},
        atomic_sc::{AtomicPtr as SCAtomicPtr, ordering::SeqCst},
        committer::Committer,
        view::SyncView,
    },
};

#[requires(*p.ward() == x)]
pub fn f<T>(x: AtomicPtr<T>, p: Ghost<Perm<AtomicPtr<T>>>) {
    x.load(ghost! {|c: &Committer<_, *mut T, Acquire, _>| {
        c.shoot_load(&p, &mut SyncView::new());
    }});
}

#[requires(*p.ward() == x)]
pub fn g<T>(x: SCAtomicPtr<T>, p: Ghost<Perm<SCAtomicPtr<T>>>) {
    x.load(ghost! {|c: &Committer<_, *mut T, SeqCst, _>| {
        c.shoot_load(&p);
    }});
}
