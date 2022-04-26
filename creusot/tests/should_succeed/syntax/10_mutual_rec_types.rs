struct Tree(Option<Box<Node>>);

struct Node {
    left: Tree,
    val: u32,
    right: Tree,
}

// To force the translation of `Tree`
fn use_tree(t: &Tree) {}

impl Tree {
    fn height(&self) -> u64 {
        match self {
            Tree(None) => 0,
            Tree(Some(n)) => n.left.height().max(n.right.height()) + 1,
        }
    }
}
