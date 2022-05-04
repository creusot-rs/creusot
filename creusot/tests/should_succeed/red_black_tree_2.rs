enum Color {
    Red,
    Black,
}

enum Tree<K,V> {
    Node {
        left: Box<Tree<K, V>>,
        color: Color,
        key: K,
        val: V,
        right: Box<Tree<K, V>>,
    },
    Leaf
}


impl<K: Ord, V> Tree<K, V> {
    fn rotate_right(&mut self) {
        match self {
            Tree::Leaf => return,
            Tree::Node { left, .. } => {
                //     self
                //    /    \
                //   x      c
                let mut x : Self = std::mem::replace(&mut * left, Tree::Leaf);
                //     self
                //         \
                //   x      c
                //
                match &mut x {
                    Tree::Leaf => return,
                    Tree::Node { right, .. } => {
                        //     self
                        //         \
                        //   x      c
                        //  / \
                        // a   b
                        std::mem::swap(left, right);
                        //        self
                        //       /    \
                        //   x  b      c
                        //  /
                        // a
                        std::mem::swap(&mut **right, self);
                        //   self
                        //  /    \
                        // a      x
                        //       / \
                        //      b   c
                    }
                }

            }
        }
    }


    fn rotate_left(&mut self) {
        match self {
            Tree::Leaf => return,
            Tree::Node { right, .. } => {
                //     self
                //    /    \
                //   a      x
                let mut x : Self = std::mem::replace(&mut * right, Tree::Leaf);
                //     self
                //    /
                //   a      x
                //
                match &mut x {
                    Tree::Leaf => return,
                    Tree::Node { left, .. } => {
                        //     self
                        //    /
                        //   a      x
                        //         / \
                        //        b   c
                        std::mem::swap(right, left);
                        //    self
                        //   /    \
                        //  a      b    x
                        //               \
                        //                c
                        std::mem::swap(&mut **left, self);
                        //        x
                        //     /     \
                        //   self     c
                        //  /    \
                        // a      b

                    }
                }

            }
        }
    }
}