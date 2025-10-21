//! Cell over predicates
//!
//! This module provides [PredCell], a wrapper around `std::cell::Cell` that allows predicates to be used to specify the contents of the cell.

use crate::{logic::Mapping, prelude::*};

/// Cell over predicates
///
/// A wrapper around `std::cell::Cell` that allows predicates to be used to specify the contents of the cell.
#[opaque]
#[repr(transparent)]
pub struct PredCell<T: ?Sized>(std::cell::Cell<T>);

impl<T: ?Sized> View for PredCell<T> {
    type ViewTy = Mapping<T, bool>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T> PredCell<T> {
    /// See the method [`Cell::new`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.new) documentation.
    #[trusted]
    #[requires(_pred[v])]
    #[ensures(result@ == *_pred)]
    pub const fn new(v: T, _pred: Snapshot<Mapping<T, bool>>) -> Self {
        Self(std::cell::Cell::new(v))
    }

    /// See the method [`Cell::set`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.set) documentation.
    #[trusted]
    #[requires(self@[v])]
    pub fn set(&self, v: T) {
        self.0.set(v)
    }

    /// See the method [`Cell::swap`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.swap) documentation.
    #[trusted]
    #[requires(forall<x: T> self@[x] == other@[x])]
    pub fn swap(&self, other: &PredCell<T>) {
        self.0.swap(&other.0)
    }

    /// See the method [`Cell::replace`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.replace) documentation.
    #[trusted]
    #[requires(self@[v])]
    #[ensures(self@[result])]
    pub const fn replace(&self, v: T) -> T {
        self.0.replace(v)
    }

    /// See the method [`Cell::into_inner`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.into_inner) documentation.
    #[trusted]
    #[ensures(self@[result])]
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: Copy> PredCell<T> {
    /// See the method [`Cell::get`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.get) documentation.
    #[trusted]
    #[ensures(self@[result])]
    pub const fn get(&self) -> T {
        self.0.get()
    }

    /// See the method [`Cell::update`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.update) documentation.
    #[trusted]
    #[requires(forall<x: T> self@[x] ==> f.precondition((x,)))]
    #[requires(forall<x: T, res: T> self@[x] && f.postcondition_once((x,), res) ==> self@[res])]
    #[ensures(exists<x: T, res: T> self@[x] && f.postcondition_once((x,), res))]
    pub fn update(&self, f: impl FnOnce(T) -> T) {
        self.0.update(f);
    }
}

impl<T: ?Sized> PredCell<T> {
    /// See the method [`Cell::from_mut`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.from_mut) documentation.
    #[trusted]
    #[requires(_pred[*t])]
    #[ensures(_pred[^t])]
    #[ensures(result@ == *_pred)]
    pub const fn from_mut(t: &mut T, _pred: Snapshot<Mapping<T, bool>>) -> &PredCell<T> {
        unsafe { std::mem::transmute(std::cell::Cell::from_mut(t)) }
    }

    // TODO: Find a way to write the `get_mut` function
}

impl<T: Default> PredCell<T> {
    /// See the method [`Cell::take`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.take) documentation.
    #[trusted]
    #[requires(forall<x: T> T::default.postcondition((), x) ==> self@[x])]
    #[ensures(self@[result])]
    pub fn take(&self) -> T {
        self.0.take()
    }
}

impl<T> PredCell<[T]> {
    /// See the method [`Cell::as_slice_of_cells`](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.as_slice_of_cells) documentation.
    #[trusted]
    #[requires(forall<s: [T]> self@[s] == (_pred.len() == s@.len() && forall<i: Int> 0 <= i && i < s@.len() ==> _pred[i][s[i]]))]
    #[ensures(forall<i: Int> 0 <= i && i < _pred.len() ==> result[i]@ == _pred[i])]
    #[ensures(result@.len() == _pred.len())]
    pub const fn as_slice_of_cells(
        &self,
        _pred: Snapshot<Seq<Mapping<T, bool>>>,
    ) -> &[PredCell<T>] {
        unsafe { std::mem::transmute(self.0.as_slice_of_cells()) }
    }
}
