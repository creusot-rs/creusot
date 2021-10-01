#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

enum Tree {
    Node(Box<Tree>, u32, Box<Tree>),
    Leaf,
}
use Tree::*;

logic! {
    fn sum_tree(t: Tree) -> Int {
        match t {
            Node(tl, a, tr) => sum_tree(*tl) + Int::from(a) + sum_tree(*tr),
            Leaf => 0,
        }
    }
}

// TODO: Make this ghost
#[ensures(sum_tree(*t) >= 0)]
fn lemma_sum_tree_nonneg(t: &Tree) {
    match t {
        Node(tl, _, tr) => {
            lemma_sum_tree_nonneg(tl);
            lemma_sum_tree_nonneg(tr);
        }
        Leaf => (),
    }
}

#[requires(sum_tree(*t) <= 1_000_000)]
#[ensures(Int::from(result) == sum_tree(*t))]
fn sum_tree_x(t: &Tree) -> u32 {
    match t {
        Node(tl, a, tr) => {
            lemma_sum_tree_nonneg(tl);
            lemma_sum_tree_nonneg(tr);
            sum_tree_x(tl) + *a + sum_tree_x(tr)
        }
        Leaf => 0,
    }
}

#[ensures(sum_tree(^mt) - sum_tree(*mt) == Int::from(^result) - Int::from(*result))]
#[ensures(Int::from(*result) <= sum_tree(*mt))]
fn take_some_tree(mt: &mut Tree) -> &mut u32 {
    match mt {
        Node(mtl, ma, mtr) => {
            lemma_sum_tree_nonneg(mtl);
            lemma_sum_tree_nonneg(mtr);
            if rand::random() {
                ma
            } else if rand::random() {
                take_some_tree(mtl)
            } else {
                take_some_tree(mtr)
            }
        }
        Leaf => loop {},
    }
}

#[requires(sum_tree(t) + Int::from(k) <= 1_000_000)]
fn inc_some_tree(mut t: Tree, k: u32) {
    let sum0 = sum_tree_x(&t);
    let ma = take_some_tree(&mut t);
    *ma += k;
    assert!(sum_tree_x(&t) == sum0 + k);
}
