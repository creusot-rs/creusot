// NO_REPLAY

extern crate creusot_std;

pub struct Tree(Option<Box<Node>>);

#[allow(dead_code)]
struct Node {
    left: Tree,
    val: u32,
    right: Tree,
}

// To force the translation of `Tree`
pub fn use_tree(_: &Tree) {}

impl Tree {
    pub fn height(&self) -> u64 {
        match self {
            Tree(None) => 0,
            Tree(Some(n)) => n.left.height().max(n.right.height()) + 1,
        }
    }
}
