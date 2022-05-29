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
    #[ensures(@result >= @self_)]
    #[ensures(@result >= @o)]
    #[ensures(result == self_ || result == o)]
    #[ensures(@self_ <= @o ==> result == o)]
    #[ensures(@o < @self_ ==> result == self_)]
    fn std::cmp::Ord::max<Self_>(self_: Self_, o: Self_) -> Self_ where
        Self_: Ord + Model,
        Self_::ModelTy: OrdLogic
}

impl Tree {
    pub fn height(&self) -> u64 {
        match self {
            Tree(None) => 0,
            Tree(Some(n)) => n.left.height().max(n.right.height()) + 1,
        }
    }
}
