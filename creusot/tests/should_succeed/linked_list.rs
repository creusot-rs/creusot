extern crate creusot_contracts;
use creusot_contracts::{
    logic::Seq,
    ptr_own::{PtrOwn, RawPtr},
    *,
};

struct Cell<T> {
    v: T,
    next: RawPtr<Cell<T>>,
}

pub struct List<T> {
    // actual data
    first: RawPtr<Cell<T>>,
    last: RawPtr<Cell<T>>,
    // ghost
    seq: GhostBox<Seq<PtrOwn<Cell<T>>>>,
}

impl<T> Invariant for List<T> {
    #[open]
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            (*self.seq == Seq::EMPTY &&
             self.first.is_null_logic() &&
             self.last.is_null_logic())
            ||
            (self.seq.len() > 0 &&
             self.first == self.seq[0].ptr() &&
             self.last  == self.seq[self.seq.len() - 1].ptr() &&
             // the cells in `seq` are chained properly
             (forall<i:Int> 0 <= i && i < self.seq.len() - 1 ==>
                 self.seq[i].val().next == self.seq[i+1].ptr()) &&
             self.seq[self.seq.len() - 1].val().next.is_null_logic())
        }
    }
}

impl<T> View for List<T> {
    type ViewTy = Seq<T>;

    #[logic]
    #[open(self)]
    fn view(self) -> Self::ViewTy {
        pearlite! {
            seq_map(*self.seq, |ptr_own: PtrOwn<Cell<T>>| ptr_own.val().v)
        }
    }
}

// TODO: see issue #1251
#[trusted]
#[pure]
#[ensures(result == x - 1)]
fn minus_one(x: Int) -> Int {
    #[allow(unreachable_code)]
    {
        loop {}
    }
}

#[logic]
#[open(self)]
pub fn seq_map<T, U>(s: Seq<T>, f: logic::Mapping<T, U>) -> Seq<U> {
    Seq::create(s.len(), |i| f.get(s[i]))
}

impl<T> List<T> {
    #[ensures(result@ == Seq::EMPTY)]
    pub fn new() -> List<T> {
        List { first: std::ptr::null(), last: std::ptr::null(), seq: Seq::new() }
    }

    #[ensures((^self)@ == (*self)@.push_back(x))]
    pub fn push_back(&mut self, x: T) {
        let cell = Box::new(Cell { v: x, next: std::ptr::null() });
        let (cell_ptr, cell_own) = PtrOwn::from_box(cell);
        if self.last.is_null() {
            self.first = cell_ptr;
            self.last = cell_ptr;
            let mut seq = self.seq.borrow_mut();
            ghost! { seq.push_back_ghost(cell_own.into_inner()) };
        } else {
            let seq = self.seq.borrow_mut();
            let cell_last = PtrOwn::as_mut(
                self.last,
                ghost! {
                    let off = minus_one(seq.len_ghost());
                    seq.into_inner().get_mut_ghost(off).unwrap()
                },
            );
            cell_last.next = cell_ptr;
            self.last = cell_ptr;
        }
    }

    #[ensures((^self)@ == (*self)@.push_front(x))]
    pub fn push_front(&mut self, x: T) {
        let (cell_ptr, cell_own) = PtrOwn::new(Cell { v: x, next: self.first });
        self.first = cell_ptr;
        if self.last.is_null() {
            self.last = cell_ptr;
        }
        let mut seq = self.seq.borrow_mut();
        ghost! { seq.push_front_ghost(cell_own.into_inner()) };
    }
}
