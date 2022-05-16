// WHY3PROVE CVC4
#![feature(box_patterns)]

extern crate creusot_contracts;
use creusot_contracts::*;
use std::mem::replace;

enum List<T> {
    Nil,
    Cons(Node<T>),
}
use List::*;
type Node<T> = Box<(T, List<T>)>;

#[logic]
fn rev_append<T>(n: List<T>, o: List<T>) -> List<T> {
    match n {
        Nil => o,
        Cons(box (hd, tl)) => rev_append(tl, Cons(Box::new((hd, o)))),
    }
}

#[ensures(^l == rev_append(*l, Nil))]
fn rev<T>(l: &mut List<T>) {
    let old_l = Ghost::record(&*l);
    let mut prev = Nil;
    let mut head = replace(l, Nil);
    #[invariant(x, rev_append(head, prev) == rev_append(@old_l, Nil))]
    while let Cons(mut curr) = head {
        let next = curr.1;
        curr.1 = prev;
        prev = Cons(curr);
        head = next;
    }
    *l = prev;
}
