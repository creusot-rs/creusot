extern crate creusot_std;
use creusot_std::{
    cell::PCell,
    ghost::{
        invariant::{
            NonAtomicInvariant, NonAtomicInvariantExt as _, Protocol, Tokens, declare_namespace,
        },
        perm::Perm,
    },
    prelude::*,
};

declare_namespace! { PERMCELL }

/// A cell that simply asserts its content's invariant.
pub struct CellInv<T> {
    data: PCell<T>,
    permission: Ghost<NonAtomicInvariant<PCellNAInv<T>>>,
}
impl<T> Invariant for CellInv<T> {
    #[logic]
    fn invariant(self) -> bool {
        self.permission.namespace() == PERMCELL() && self.permission.public() == self.data
    }
}

struct PCellNAInv<T>(Perm<PCell<T>>);
impl<T> Protocol for PCellNAInv<T> {
    type Public = PCell<T>;

    #[logic]
    fn public(self) -> Self::Public {
        *self.0.ward()
    }

    #[logic]
    fn protocol(self) -> bool {
        true
    }
}

impl<T> CellInv<T> {
    #[requires(tokens.contains(PERMCELL()))]
    pub unsafe fn read<'a>(&'a self, tokens: Ghost<Tokens<'a>>) -> &'a T {
        self.permission
            .open(tokens, move |perm| unsafe { self.data.borrow(ghost!(&perm.into_inner().0)) })
    }

    #[requires(tokens.contains(PERMCELL()))]
    pub unsafe fn write(&self, x: T, tokens: Ghost<Tokens>) {
        self.permission.open(tokens, move |perm| unsafe {
            *self.data.borrow_mut(ghost!(&mut perm.into_inner().0)) = x
        })
    }
}
