extern crate creusot_contracts;

use creusot_contracts::*;

pub struct Tree(Option<Box<Node>>);

#[allow(dead_code)]
struct Node {
    left: Tree,
    val: u32,
    right: Tree,
}

// To force the translation of `Tree`
pub fn use_tree(_: &Tree) {}

extern_spec! {
    mod std {
        mod cmp {
            trait Ord where Self: Model, Self::ModelTy: OrdLogic {
                #[ensures(@result >= @self_)]
                #[ensures(@result >= @rhs)]
                #[ensures(result == self_ || result == rhs)]
                #[ensures(@self_ <= @rhs ==> result == rhs)]
                #[ensures(@rhs < @self_ ==> result == self_)]
                fn max(self, rhs: Self) -> Self ;
            }
        }
    }
}

impl Tree {
    pub fn height(&self) -> u64 {
        match self {
            Tree(None) => 0,
            Tree(Some(n)) => n.left.height().max(n.right.height()) + 1,
        }
    }
}
