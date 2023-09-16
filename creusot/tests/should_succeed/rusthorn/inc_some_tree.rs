extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

pub enum Tree {
    Node(Box<Tree>, u32, Box<Tree>),
    Leaf,
}
use Tree::*;

// FIXME: this should go away, we have not defined any order relation on Tree
#[trusted]
impl WellFounded for Tree {}

#[trusted]
fn random() -> bool {
    panic!()
}

impl Tree {
    #[ghost]
    fn sum(self) -> Int {
        pearlite! {
            match self {
                Node(tl, a, tr) => tl.sum() + a@ + tr.sum(),
                Leaf => 0,
            }
        }
    }

    #[ghost]
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
    #[ensures(result@ == self.sum())]
    fn sum_x(&self) -> u32 {
        match self {
            Node(tl, a, tr) => {
                proof_assert! {
                    tl.lemma_sum_nonneg();
                    tr.lemma_sum_nonneg();
                    true
                };
                tl.sum_x() + *a + tr.sum_x()
            }
            Leaf => 0,
        }
    }

    #[ensures((^self).sum() - self.sum() == (^result)@ - result@)]
    #[ensures(result@ <= self.sum())]
    fn take_some(&mut self) -> &mut u32 {
        match self {
            Node(mtl, ma, mtr) => {
                proof_assert! {
                    mtl.lemma_sum_nonneg();
                    mtr.lemma_sum_nonneg();
                    true
                };
                if random() {
                    ma
                } else if random() {
                    mtl.take_some()
                } else {
                    mtr.take_some()
                }
            }
            Leaf => loop {},
        }
    }
}

#[requires(t.sum() + k@ <= 1_000_000)]
pub fn inc_some_tree(mut t: Tree, k: u32) {
    let sum0 = t.sum_x();
    let ma = t.take_some();
    *ma += k;
    assert!(t.sum_x() == sum0 + k);
}
