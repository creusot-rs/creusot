extern crate creusot_contracts;
use ::std::rc::Rc;
use creusot_contracts::{cell::PermCell, ghost::perm::Perm, prelude::*};

pub struct Node<T> {
    next: Rc<PermCell<List<T>>>,
}
pub struct List<T> {
    head: Option<Node<T>>,
}

impl<T> List<T> {
    #[requires(false)]
    pub fn foo(&mut self, mut perm: Ghost<Perm<PermCell<List<T>>>>) {
        let mut p = self;
        let mut next;

        while !p.head.is_none() {
            let curr = p.head.take().unwrap();
            next = curr.next.clone();
            unsafe {
                p = next.as_ref().borrow_mut(perm.borrow_mut());
            }
        }
    }
}
