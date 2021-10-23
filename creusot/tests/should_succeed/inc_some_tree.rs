extern crate creusot_contracts;
use creusot_contracts::*;

enum Tree {
    Node(Box<Tree>, u32, Box<Tree>),
    Leaf,
}
use Tree::*;
impl WellFounded for Tree {}

impl Tree {
    #[logic]
    fn sum(self) -> Int {
        match self {
            Node(tl, a, tr) => tl.sum() + a.model() + tr.sum(),
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
    #[ensures(@result == self.sum())]
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

    #[ensures((^self).sum() - self.sum() == @^result - @result)]
    #[ensures(@result <= self.sum())]
    fn take_some(&mut self) -> &mut u32 {
        match self {
            Node(mtl, ma, mtr) => {
                mtl.lemma_sum_nonneg();
                mtr.lemma_sum_nonneg();
                if rand::random() {
                    ma
                } else if rand::random() {
                    mtl.take_some()
                } else {
                    mtr.take_some()
                }
            }
            Leaf => loop {},
        }
    }
}

#[requires(t.sum() + @k <= 1_000_000)]
fn inc_some_tree(mut t: Tree, k: u32) {
    let sum0 = t.sum_x();
    let ma = t.take_some();
    *ma += k;
    assert!(t.sum_x() == sum0 + k);
}
