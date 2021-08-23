use crate as creusot_contracts;
use creusot_contracts_proc::*;

#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "equal"]
pub fn equal<T>(_: T, _: T) -> bool {
    panic!();
}

pub struct Int;

impl PartialEq for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "eq_int"]
    fn eq(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "ne_int"]
    fn ne(&self, _: &Int) -> bool {
        panic!()
    }
}

impl PartialOrd for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "le_int"]
    fn le(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "ge_int"]
    fn ge(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "lt_int"]
    fn lt(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "gt_int"]
    fn gt(&self, _: &Int) -> bool {
        panic!()
    }

    #[creusot::spec::no_translate]
    fn partial_cmp(&self, _: &Self) -> Option<std::cmp::Ordering> {
        panic!()
    }
}

impl From<i32> for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "i32_to_int"]
    fn from(_: i32) -> Self {
        panic!()
    }
}

impl From<u32> for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "u32_to_int"]
    fn from(_: u32) -> Self {
        panic!()
    }
}

impl From<usize> for Int {
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "usize_to_int"]
    fn from(_: usize) -> Self {
        panic!()
    }
}

use std::ops::*;

impl Add<Int> for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "add_int"]
    fn add(self, _: Int) -> Self {
        panic!()
    }
}

impl Sub<Int> for Int {
    type Output = Int;
    #[creusot::spec::no_translate]
    #[rustc_diagnostic_item = "sub_int"]
    fn sub(self, _: Int) -> Self {
        panic!()
    }
}

#[rustc_diagnostic_item = "creusot_resolve"]
pub unsafe trait Resolve {
    predicate! {
        #[rustc_diagnostic_item = "creusot_resolve_method"]
        fn resolve(self) -> bool;
    }
}

unsafe impl Resolve for u32 {
    predicate! { fn resolve(self) -> bool {
        true
    } }
}

unsafe impl Resolve for usize {
    predicate! { fn resolve(self) -> bool {
        true
    } }
}

unsafe impl Resolve for i32 {
    predicate! { fn resolve(self) -> bool {
        true
    } }
}

unsafe impl Resolve for isize {
    predicate! { fn resolve(self) -> bool {
        true
    } }
}

unsafe impl Resolve for () {
    predicate! { fn resolve(self) -> bool {
        true
    } }
}

unsafe impl Resolve for bool {
    predicate! { fn resolve(self) -> bool {
        true
    } }
}

unsafe impl<T> Resolve for &T {
    predicate! { fn resolve(self) -> bool {
        true
    } }
}

unsafe impl<T1: Resolve, T2: Resolve> Resolve for (T1, T2) {
    predicate! { fn resolve(self) -> bool { {
        Resolve::resolve(self.0) && Resolve::resolve(self.1)
        // TODO: Figure out why `resolve` isn't... resolving in the type checker
        // p1.resolve() && p2.resolve()
    } }}
}

unsafe impl<T> Resolve for &mut T {
    predicate! { fn resolve(self) -> bool {
        equal(^ self, * self)
    } }
}
