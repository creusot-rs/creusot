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
impl WellFounded for Tree {}

impl Tree {
    #[logic_rust]
    fn sum(self) -> Int {
        match self {
            Node(tl, a, tr) => tl.sum() + Int::from(a) + tr.sum(),
            Leaf => 0,
        }
    }

    // TODO: Make this ghost
    #[pure]
    #[variant(*self)]
    #[ensures(self.sum() >= 0)]
    fn lemma_sum_nonneg(&self) {
        match self {
            Node(tl, _, tr) => {
                tl.lemma_sum_nonneg();
                tr.lemma_sum_nonneg();
            }
            Leaf => (),
        }
    }

    #[requires(self.sum() <= 1_000_000)]
    #[ensures(Int::from(result) == self.sum())]
    fn sum_x(&self) -> u32 {
        match self {
            Node(tl, a, tr) => {
                tl.lemma_sum_nonneg();
                tr.lemma_sum_nonneg();
                tl.sum_x() + *a + tr.sum_x()
            }
            Leaf => 0,
        }
    }

    #[ensures((^self).sum() - self.sum() ==
        Int::from(^result.0) + (^result.1).sum() - Int::from(*result.0) - (*result.1).sum())]
    #[ensures(Int::from(*result.0) <= self.sum())]
    #[ensures(result.1.sum() <= self.sum())]
    fn take_some_rest(&mut self) -> (&mut u32, &mut Tree) {
        match self {
            Node(mtl, ma, mtr) => {
                mtl.lemma_sum_nonneg();
                mtr.lemma_sum_nonneg();
                if rand::random() {
                    (ma, if rand::random() { mtl } else { mtr })
                } else if rand::random() {
                    mtl.take_some_rest()
                } else {
                    mtr.take_some_rest()
                }
            }
            Leaf => loop {},
        }
    }
}

#[requires(t.sum() + Int::from(j) + Int::from(k) <= 1_000_000)]
fn inc_some_2_tree(mut t: Tree, j: u32, k: u32) {
    let sum0 = t.sum_x();
    let (ma, mt) = t.take_some_rest();
    let (mb, _) = mt.take_some_rest();
    *ma += j;
    *mb += k;
    assert!(t.sum_x() == sum0 + j + k);
}
