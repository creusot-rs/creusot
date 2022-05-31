#![allow(unused_variables)]

extern crate creusot_contracts;

trait Omg {
    fn test(self);
}

impl Omg for () {
    fn test(self) {}
}

trait GenericMethod {
    fn meth<F>(&self, f: F);
}

impl<T> GenericMethod for [T] {
    fn meth<F>(&self, f: F) {}
}

pub fn omg(x: &mut [u32]) {
    let _ = x.len();
}
