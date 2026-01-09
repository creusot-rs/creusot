extern crate creusot_std;
use creusot_std::{
    cell::PermCell,
    ghost::{
        local_invariant::{
            LocalInvariant, LocalInvariantExt as _, Protocol, Tokens, declare_namespace,
        },
        perm::Perm,
    },
    prelude::*,
};

declare_namespace! { PERMCELL }

/// A cell that simply asserts its content's invariant.
pub struct CellInv<T> {
    data: PermCell<T>,
    permission: Ghost<LocalInvariant<PermCellLocalInv<T>>>,
}
impl<T> Invariant for CellInv<T> {
    #[logic]
    fn invariant(self) -> bool {
        self.permission.namespace() == PERMCELL() && self.permission.public() == self.data
    }
}

struct PermCellLocalInv<T>(Box<Perm<PermCell<T>>>);
impl<T> Protocol for PermCellLocalInv<T> {
    type Public = PermCell<T>;

    #[logic]
    fn protocol(self, pc: PermCell<T>) -> bool {
        *self.0.ward() == pc
    }
}

impl<T> CellInv<T> {
    #[requires(tokens.contains(PERMCELL()))]
    pub fn read<'a>(&'a self, tokens: Ghost<Tokens<'a>>) -> &'a T {
        self.permission
            .open(tokens, move |perm| unsafe { self.data.borrow(ghost!(&perm.into_inner().0)) })
    }

    #[requires(tokens.contains(PERMCELL()))]
    pub fn write(&self, x: T, tokens: Ghost<Tokens>) {
        self.permission.open(tokens, move |perm| unsafe {
            *self.data.borrow_mut(ghost!(&mut perm.into_inner().0)) = x
        })
    }
}
