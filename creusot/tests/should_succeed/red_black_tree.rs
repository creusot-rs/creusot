#[derive(Clone, Copy)]
enum Color {
    Red,
    Black,
}

impl Color {
    fn flip(self) -> Self {
        match self {
            Color::Black => Color::Red,
            Color::Red => Color::Black,
        }
    }
}

struct Node<K, V> {
    left: Tree<K, V>,
    color: Color,
    key: K,
    val: V,
    right: Tree<K, V>,
}

struct Tree<K, V> {
    node: Option<Box<Node<K, V>>>,
}

impl<K: Ord, V> Node<K, V> {
    fn rotate_right(&mut self) {
        //     self
        //    /    \
        //   x      c
        //  / \
        // a   b
        // Rip out the left subtree
        let mut x: Box<_> = match std::mem::take(&mut self.left.node) {
            Some(x) => x,
            None => return,
        };
        //     self
        //         \
        //   x      c
        //  / \
        // a   b
        std::mem::swap(&mut self.left, &mut x.right);
        //        self
        //       /    \
        //   x  b      c
        //  /
        // a
        std::mem::swap(self, &mut x);
        //   self
        //  /
        // a      x
        //       / \
        //      b   c
        self.right = Tree { node: Some(x) };
        //   self
        //  /    \
        // a      x
        //       / \
        //      b   c
    }

    fn rotate_left(&mut self) {
        let mut x: Box<_> = match std::mem::take(&mut self.right.node) {
            Some(x) => x,
            None => return,
        };
        std::mem::swap(&mut x.right, &mut self.left);
        std::mem::swap(self, &mut x);
        self.left = Tree { node: Some(x) };
    }

    fn flip_colors(&mut self) {
        self.color = self.color.flip();

        let left = self.left.unwrap_mut();
        left.color = left.color.flip();

        let right = self.right.unwrap_mut();
        right.color = right.color.flip();
    }
}

impl<K: Ord, V> Tree<K, V> {
    fn insert(&mut self, key: K, val: V) {
        if let None = self.node {}

        use std::cmp::Ordering;
        let node = self.unwrap_mut();
        match key.cmp(&node.key) {
            Ordering::Less => node.left.insert(key, val),
            Ordering::Equal => node.val = val,
            Ordering::Greater => node.left.insert(key, val),
        }

        if node.right.is_red() && !node.left.is_red() {
            node.rotate_left();
        }

        if node.left.is_red() && !node.left.unwrap_mut().left.is_red() {
            node.rotate_right();
        }

        if node.left.is_red() && node.right.is_red() {
            node.flip_colors();
        }
    }

    fn unwrap_mut(&mut self) -> &mut Node<K, V> {
        self.node.as_mut().unwrap()
    }

    fn is_red(&self) -> bool {
        match &self.node {
            None => false,
            Some(n) => matches!(n.color, Color::Red),
        }
    }

    fn is_black(&self) -> bool {
        match &self.node {
            None => true,
            Some(n) => matches!(n.color, Color::Black),
        }
    }
}
