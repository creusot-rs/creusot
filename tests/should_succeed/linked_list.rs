extern crate creusot_contracts;
use creusot_contracts::{ghost::perm::Perm, prelude::*};

struct Link<T> {
    value: T,
    next: *const Link<T>,
}

pub struct List<T> {
    // actual data
    first: *const Link<T>,
    last: *const Link<T>,
    // ghost
    seq: Ghost<Seq<Box<Perm<*const Link<T>>>>>,
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
             // the links in `seq` are chained properly
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
            (*self.seq).map(|ptr_perm: Box<Perm<*const Link<T>>>| ptr_perm.val().value)
        }
    }
}

impl<T> List<T> {
    #[ensures(result@ == Seq::empty())]
    pub fn new() -> List<T> {
        List { first: std::ptr::null(), last: std::ptr::null(), seq: Seq::new() }
    }

    #[ensures((^self)@ == (*self)@.push_back(value))]
    pub fn push_back(&mut self, value: T) {
        let link = Box::new(Link { value, next: std::ptr::null() });
        let (link_ptr, link_own) = Perm::from_box(link);
        if self.last.is_null() {
            self.first = link_ptr;
            self.last = link_ptr;
        } else {
            let link_last = unsafe {
                Perm::as_mut(
                    self.last as *mut Link<T>,
                    ghost! {
                        let off = self.seq.len_ghost() - 1int;
                        self.seq.get_mut_ghost(off).unwrap()
                    },
                )
            };
            link_last.next = link_ptr;
            self.last = link_ptr;
        }
        ghost! { self.seq.push_back_ghost(link_own.into_inner()) };
    }

    #[ensures((^self)@ == (*self)@.push_front(value))]
    pub fn push_front(&mut self, value: T) {
        let (link_ptr, link_own) = Perm::new(Link { value, next: self.first });
        self.first = link_ptr;
        if self.last.is_null() {
            self.last = link_ptr;
        }
        ghost! { self.seq.push_front_ghost(link_own.into_inner()) };
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
        let link = unsafe { *Perm::to_box(self.first as *mut Link<T>, own) };
        self.first = link.next;
        if self.first.is_null() {
            self.last = std::ptr::null_mut();
        }
        Some(link.value)
    }
}
