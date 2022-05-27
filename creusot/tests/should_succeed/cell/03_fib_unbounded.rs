// UNBOUNDED
extern crate creusot_contracts;

use creusot_contracts::*;

pub trait Inv<T> {
    #[predicate]
    fn inv(&self, x: T) -> bool;
}

pub struct Cell<T, I> {
    inner: std::cell::Cell<T>,
    // Pretend that `I` is ghost
    ghost_inv: I,
}

impl<T: Copy, I: Inv<T>> Cell<T, I> {
    #[trusted]
    #[ensures(self.ghost_inv.inv(result))]
    pub fn get(&self) -> T {
        self.inner.get()
    }

    #[trusted]
    #[requires(self.ghost_inv.inv(v))]
    pub fn set(&self, v: T) {
        self.inner.set(v)
    }
}

// TODO: this function shouldn't actually be pure, the program version will abort.
#[logic]
#[variant(i)]
fn fib(i: Int) -> Int {
    if i <= 0 {
        0
    } else if i == 1 {
        1
    } else {
        fib(i - 1) + fib(i - 2)
    }
}

pub struct Fib {
    ix: usize,
}
impl Inv<Option<usize>> for Fib {
    #[predicate]
    fn inv(&self, v: Option<usize>) -> bool {
        pearlite! {
            match v {
                None => true,
                Some(i) => @i == fib(@self.ix)
            }
        }
    }
}

pub type FibCache = Vec<Cell<Option<usize>, Fib>>;

#[predicate]
fn fib_cell(v: FibCache) -> bool {
    pearlite! {
        forall<i : Int> @(@v)[i].ghost_inv.ix == i
    }
}

#[requires(fib_cell(*mem))]
#[requires(@i < (@mem).len())]
#[ensures(@result == fib(@i))]
#[requires(0 <= @i)]
pub fn fib_memo(mem: &FibCache, i: usize) -> usize {
    match mem[i].get() {
        Some(v) => v,
        None => {
            let fib_i = if i == 0 {
                0
            } else if i == 1 {
                1
            } else {
                fib_memo(mem, i - 1) + fib_memo(mem, i - 2)
            };
            proof_assert! { @fib_i == fib(@i)};
            mem[i].set(Some(fib_i));
            fib_i
        }
    }
}
