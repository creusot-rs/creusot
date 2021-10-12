#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;
use std::marker::PhantomData;

trait Inv<T> {
    #[predicate]
    fn inv(x: T) -> bool;
}

struct Cell<T, I> {
    inner: std::cell::Cell<T>,
    inv: PhantomData<I>,
}

impl<T: Copy, I: Inv<T>> Cell<T, I> {
    #[trusted]
    #[ensures(I::inv(result))]
    fn get(&self) -> T {
        self.inner.get()
    }

    #[trusted]
    #[requires(I::inv(v))]
    fn set(&self, v: T) {
        self.inner.set(v)
    }
}

struct Even;

impl Inv<u32> for Even {
    #[predicate]
    fn inv(x: u32) -> bool {
        x % 2u32 == 0u32
    }
}

fn adds_two(c: &Cell<u32, Even>) {
    let v = c.get();
    // To shut up overflow checking
    if v < 100000 {
        c.set(v + 2);
    } else {
        c.set(0);
    }
}
