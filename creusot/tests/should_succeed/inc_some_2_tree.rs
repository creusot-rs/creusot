extern crate creusot_contracts;
use creusot_contracts::*;

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
    #[logic]
    fn sum(self) -> Int {
        match self {
            Node(tl, a, tr) => tl.sum() + a.model() + tr.sum(),
            Leaf => 0,
        }
    }

    #[logic]
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

    #[ensures((^self).sum() - self.sum() ==
        @^result.0 + (^result.1).sum() - @result.0 - (*result.1).sum())]
    #[ensures(@result.0 <= self.sum())]
    #[ensures(result.1.sum() <= self.sum())]
    fn take_some_rest(&mut self) -> (&mut u32, &mut Tree) {
        match self {
            Node(mtl, ma, mtr) => {
                proof_assert! {
                    mtl.lemma_sum_nonneg();
                    mtr.lemma_sum_nonneg();
                    true
                };
                if random() {
                    (ma, if random() { mtl } else { mtr })
                } else if random() {
                    mtl.take_some_rest()
                } else {
                    mtr.take_some_rest()
                }
            }
            Leaf => loop {},
        }
    }
}

#[requires(t.sum() + @j + @k <= 1_000_000)]
pub fn inc_some_2_tree(mut t: Tree, j: u32, k: u32) {
    let sum0 = t.sum_x();
    let (ma, mt) = t.take_some_rest();
    let (mb, _) = mt.take_some_rest();
    *ma += j;
    *mb += k;
    assert!(t.sum_x() == sum0 + j + k);
}
