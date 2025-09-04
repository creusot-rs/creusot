//! Cell over predicates
//!
//! This module provides a wrapper around `std::cell::Cell` that allows predicates to be used to specify the contents of the cell.

// TODO: Rust 1.88: Add `const fn` + `update` method.

use crate::{logic::Mapping, *};

#[trusted]
#[repr(transparent)]
pub struct PredCell<T: ?Sized>(std::cell::Cell<T>);

impl<T: ?Sized> View for PredCell<T> {
    type ViewTy = Mapping<T, bool>;

    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T> PredCell<T> {
    /// See the method [new](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.new) documentation.
    #[trusted]
    #[requires(_m[v])]
    #[ensures(result@ == *_m)]
    pub fn new(v: T, _m: Snapshot<Mapping<T, bool>>) -> Self {
        Self(std::cell::Cell::new(v))
    }

    /// See the method [set](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.set) documentation.
    #[trusted]
    #[requires(self@[v])]
    pub fn set(&self, v: T) {
        self.0.set(v)
    }

    /// See the method [swap](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.swap) documentation.
    #[trusted]
    #[requires(forall<x: T> self@[x] == other@[x])]
    pub fn swap(&self, other: &PredCell<T>) {
        self.0.swap(&other.0)
    }

    /// See the method [replace](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.replace) documentation.
    #[trusted]
    #[requires(self@[v])]
    #[ensures(self@[result])]
    pub fn replace(&self, v: T) -> T {
        self.0.replace(v)
    }

    /// See the method [into_inner](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.into_inner) documentation.
    #[trusted]
    #[ensures(self@[result])]
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: Copy> PredCell<T> {
    /// See the method [get](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.get) documentation.
    #[trusted]
    #[ensures(self@[result])]
    pub fn get(&self) -> T {
        self.0.get()
    }

    /// See the method [update](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.update) documentation.
    #[trusted]
    #[requires(forall<x: T> self@[x] ==> f.precondition((x,)))]
    #[requires(forall<x: T, res: T> self@[x] && f.postcondition_once((x,), res) ==> self@[res])]
    #[ensures(exists<x: T, res: T> self@[x] && f.postcondition_once((x,), res))]
    pub fn update(&self, f: impl FnOnce(T) -> T) {
        self.0.update(f);
    }
}

impl<T: ?Sized> PredCell<T> {
    /// See the method [from_mut](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.from_mut) documentation.
    #[trusted]
    #[requires(_m[*t])]
    #[ensures(_m[^t])]
    #[ensures(result@ == *_m)]
    pub fn from_mut(t: &mut T, _m: Snapshot<Mapping<T, bool>>) -> &PredCell<T> {
        unsafe { std::mem::transmute(std::cell::Cell::from_mut(t)) }
    }

    // TODO: Find a way to write the `get_mut` function
}

impl<T: Default> PredCell<T> {
    /// See the method [take](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.take) documentation.
    #[trusted]
    #[requires(forall<x: T> T::default.postcondition((), x) ==> self@[x])]
    #[ensures(self@[result])]
    pub fn take(&self) -> T {
        self.0.take()
    }
}

impl<T> PredCell<[T]> {
    /// See the method [as_slice_of_cells](https://doc.rust-lang.org/std/cell/struct.Cell.html#method.as_slice_of_cells) documentation.
    #[trusted]
    #[requires(forall<s: [T]> self@[s] == (_m.len() == s@.len() && forall<i: Int> 0 <= i && i < s@.len() ==> _m[i][s[i]]))]
    #[ensures(forall<i: Int> 0 <= i && i < _m.len() ==> result[i]@ == _m[i])]
    #[ensures(result@.len() == _m.len())]
    pub fn as_slice_of_cells(&self, _m: Snapshot<Seq<Mapping<T, bool>>>) -> &[PredCell<T>] {
        unsafe { std::mem::transmute(self.0.as_slice_of_cells()) }
    }
}
