// UNBOUNDED
extern crate creusot_contracts;
use creusot_contracts::*;

// Ensures that the 'spec' axiom is built up correctly:
// 1. Preconditions turn into implications
// 2. Postconditions turn into conjunction
#[pure]
#[requires(false)]
#[requires(false)]
#[requires(false)]
#[ensures(true)]
#[ensures(true)]
#[ensures(true)]
fn pure_declaration(x: u32, y: u64) {
    ()
}

enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

impl<T> WellFounded for List<T> {}
use List::*;

impl<T> List<T> {
    #[pure]
    #[ensures(result >= 0usize)]
    #[variant(*self)]
    fn len(&self) -> usize {
        match self {
            Cons(_, ls) => 1 + ls.len(),
            Nil => 0,
        }
    }
}

#[requires(l.len() <= 10usize)]
#[ensures(result <= 10usize)]
fn test<T>(l: &List<T>) -> usize {
    l.len()
}

#[logic]
fn uses_len<T>(l: List<T>) -> Int {
    l.len().model()
}

#[ensures(@result === uses_len(l))]
fn uses_both_logic_and_prog<T>(l: List<T>) -> usize {
    l.len()
}
