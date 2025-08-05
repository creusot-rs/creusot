extern crate creusot_contracts;
use creusot_contracts::{
    local_invariant::{
        LocalInvariant, LocalInvariantExt as _, LocalInvariantSpec, Namespaces, declare_namespace,
    },
    logic::Id,
    pcell::{PCell, PCellOwn},
    *,
};

declare_namespace! { PCELL }

/// A cell that simply asserts its content's invariant.
pub struct CellInv<T: Invariant> {
    data: PCell<T>,
    permission: Ghost<LocalInvariant<PCellLocalInv<T>>>,
}
impl<T: Invariant> Invariant for CellInv<T> {
    #[logic]
    fn invariant(self) -> bool {
        self.permission.namespace() == PCELL() && self.permission.public() == self.data.id()
    }
}

struct PCellLocalInv<T>(PCellOwn<T>);
impl<T: Invariant> LocalInvariantSpec for PCellLocalInv<T> {
    type Public = Id;

    #[logic]
    fn invariant_with_data(self, id: Id) -> bool {
        self.0.id() == id
    }
}

impl<T: Invariant> CellInv<T> {
    #[requires(namespaces.contains(PCELL()))]
    pub fn read<'a>(&'a self, namespaces: Ghost<Namespaces<'a>>) -> &'a T {
        self.permission
            .open(namespaces, move |perm| unsafe { self.data.borrow(ghost!(&perm.into_inner().0)) })
    }

    #[requires(namespaces.contains(PCELL()))]
    pub fn write(&self, x: T, namespaces: Ghost<Namespaces>) {
        self.permission.open(namespaces, move |perm| unsafe {
            *self.data.borrow_mut(ghost!(&mut perm.into_inner().0)) = x
        })
    }
}
