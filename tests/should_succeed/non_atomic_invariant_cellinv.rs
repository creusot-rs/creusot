extern crate creusot_std;
use creusot_std::{
    cell::PCell,
    ghost::{
        invariant::{NonAtomicInvariant, Protocol, Tokens, declare_namespace},
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
    pub fn read<'a>(&'a self, tokens: Ghost<&'a Tokens<'a>>) -> &'a T {
        unsafe { self.data.borrow(ghost!(&self.permission.open_const(tokens.into_inner()).0)) }
    }

    #[requires(tokens.contains(PERMCELL()))]
    pub fn write(&self, x: T, tokens: Ghost<Tokens>) {
        ghost_let!(perm = &mut self.permission.open(tokens.into_inner()).inner.0);
        unsafe { *self.data.borrow_mut(perm) = x }
    }
}
