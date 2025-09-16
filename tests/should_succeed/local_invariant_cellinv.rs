extern crate creusot_contracts;
use creusot_contracts::{
    cell::{PermCell, PermCellOwn},
    ghost::local_invariant::{
        LocalInvariant, LocalInvariantExt as _, Protocol, Tokens, declare_namespace,
    },
    logic::Id,
    *,
};

declare_namespace! { PERMCELL }

/// A cell that simply asserts its content's invariant.
pub struct CellInv<T: Invariant> {
    data: PermCell<T>,
    permission: Ghost<LocalInvariant<PermCellLocalInv<T>>>,
}
impl<T: Invariant> Invariant for CellInv<T> {
    #[logic]
    fn invariant(self) -> bool {
        self.permission.namespace() == PERMCELL() && self.permission.public() == self.data.id()
    }
}

struct PermCellLocalInv<T>(PermCellOwn<T>);
impl<T: Invariant> Protocol for PermCellLocalInv<T> {
    type Public = Id;

    #[logic]
    fn protocol(self, id: Id) -> bool {
        self.0.id() == id
    }
}

impl<T: Invariant> CellInv<T> {
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
