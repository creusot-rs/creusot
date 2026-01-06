extern crate creusot_contracts;
use creusot_contracts::{ghost::perm::Perm, prelude::*};

struct Cell<T> {
    v: T,
    next: *const Cell<T>,
}

pub struct List<T> {
    // actual data
    first: *const Cell<T>,
    last: *const Cell<T>,
    // ghost
    seq: Ghost<Seq<Box<Perm<*const Cell<T>>>>>,
}

impl<T> Invariant for List<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            (*self.seq == Seq::empty() &&
             self.first.is_null_logic() &&
             self.last.is_null_logic())
            ||
            (self.seq.len() > 0 &&
             self.first == *self.seq[0].ward() &&
             self.last  == *self.seq[self.seq.len() - 1].ward() &&
             // the cells in `seq` are chained properly
             (forall<i> 0 <= i && i < self.seq.len() - 1 ==>
                 self.seq[i].val().next == *self.seq[i+1].ward()) &&
             self.seq[self.seq.len() - 1].val().next.is_null_logic())
        }
    }
}

impl<T> View for List<T> {
    type ViewTy = Seq<T>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        pearlite! {
            (*self.seq).map(|ptr_perm: Box<Perm<*const Cell<T>>>| ptr_perm.val().v)
        }
    }
}

impl<T> List<T> {
    #[ensures(result@ == Seq::empty())]
    pub fn new() -> List<T> {
        List { first: std::ptr::null(), last: std::ptr::null(), seq: Seq::new() }
    }

    #[ensures((^self)@ == (*self)@.push_back(x))]
    pub fn push_back(&mut self, x: T) {
        let cell = Box::new(Cell { v: x, next: std::ptr::null() });
        let (cell_ptr, cell_own) = Perm::from_box(cell);
        if self.last.is_null() {
            self.first = cell_ptr;
            self.last = cell_ptr;
        } else {
            let cell_last = unsafe {
                Perm::as_mut(
                    self.last as *mut Cell<T>,
                    ghost! {
                        let off = self.seq.len_ghost() - 1int;
                        self.seq.get_mut_ghost(off).unwrap()
                    },
                )
            };
            cell_last.next = cell_ptr;
            self.last = cell_ptr;
        }
        ghost! { self.seq.push_back_ghost(cell_own.into_inner()) };
    }

    #[ensures((^self)@ == (*self)@.push_front(x))]
    pub fn push_front(&mut self, x: T) {
        let (cell_ptr, cell_own) = Perm::new(Cell { v: x, next: self.first });
        self.first = cell_ptr;
        if self.last.is_null() {
            self.last = cell_ptr;
        }
        ghost! { self.seq.push_front_ghost(cell_own.into_inner()) };
    }

    #[ensures(match result {
        None => (*self)@ == Seq::empty() && (^self)@ == Seq::empty(),
        Some(x) => (*self)@.len() > 0 && x == (*self)@[0] && (^self)@ == (*self)@.pop_front()
    })]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.first.is_null() {
            return None;
        }
        let own = ghost! { self.seq.pop_front_ghost().unwrap() };
        let cell = unsafe { *Perm::to_box(self.first as *mut Cell<T>, own) };
        self.first = cell.next;
        if self.first.is_null() {
            self.last = std::ptr::null_mut();
        }
        Some(cell.v)
    }
}
