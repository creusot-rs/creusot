#![feature(box_patterns)]
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;
use std::cmp::Ordering::*;
use std::cmp::Ord;

extern_spec! {
    #[ensures(result === (@self_).cmp_log(@*o))]
    fn std::cmp::Ord::cmp<T>(self_: &T, o: &T) -> Ordering
        where T: Ord,
              T: Model,
              T::ModelTy: OrdLogic
}

#[derive(Clone, Copy)]
enum Color {
    Red,
    Black,
}
use Color::*;

impl Color {
    #[ensures(result === self.flip_log())]
    fn flip(self) -> Self {
        match self {
            Black => Red,
            Red => Black,
        }
    }

    #[logic]
    fn flip_log(self) -> Self {
        pearlite! {
            match self {
                Black => Red,
                Red => Black,
            }
        }
    }

    #[ensures(^self === (*self).flip_log())]
    fn flip_mut(&mut self) {
        *self = self.flip()
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

impl<K: Model, V> Node<K, V> where K::ModelTy: OrdLogic {
    #[requires(!(self.left.node === None))]
    #[requires((*self).ord_invariant())]
    #[ensures(@*self === @^self)]
    #[ensures((^self).ord_invariant())]
    fn rotate_right(&mut self) {
        //     self
        //    /    \
        //   x      c
        //  / \
        // a   b
        // Rip out the left subtree
        let mut x: Box<_> = match std::mem::replace(&mut self.left.node, None) {
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

    #[requires(!(self.right.node === None))]
    #[requires((*self).ord_invariant())]
    #[ensures(@*self === @^self)]
    #[ensures((^self).ord_invariant())]
    fn rotate_left(&mut self) {
        let mut x: Box<_> = match std::mem::replace(&mut self.right.node, None) {
            Some(x) => x,
            None => return,
        };
        std::mem::swap(&mut self.right, &mut x.left);
        std::mem::swap(self, &mut x);
        self.left = Tree { node: Some(x) };
    }

    #[requires((*self).ord_invariant())]
    #[ensures(@*self === @^self)]
    #[ensures((*self).left === (^self).left)]
    #[ensures((*self).right === (^self).right)]
    #[ensures((^self).ord_invariant())]
    fn flip_color(&mut self) {
        self.color.flip_mut();
    }

   #[predicate]
    fn ord_invariant_here(self) -> bool {
        pearlite! {
            forall<key: K::ModelTy>
                ((@self.left).get(key) === None  || key <= @self.key) &&
                ((@self.right).get(key) === None || @self.key <= key)
        }
    }

    #[predicate]
    fn ord_invariant(self) -> bool {
        pearlite! {
            self.ord_invariant_here() && self.left.ord_invariant() && self.right.ord_invariant()
        }
    }
}

impl<K: Model, V> Tree<K, V> where K::ModelTy: OrdLogic {
    #[ensures(@result === Mapping::cst(None))]
    #[ensures(result.ord_invariant())]
    fn new() -> Tree<K, V> {
        Tree { node: None }
    }

    #[requires((*self).ord_invariant())]
    #[ensures((^self).ord_invariant())]
    #[ensures(@^self === (@*self).set(@key, Some(val)))]
    fn insert(&mut self, key: K, val: V) where K: Ord {
        match &mut self.node {
            None => {
                self.node = Some(Box::new(Node {
                    left: Tree { node: None },
                    color: Black,
                    key,
                    val,
                    right: Tree { node: None }}));
                return
            },
            Some(node) => {
                proof_assert! { node.model_left_right(@key /* dummy */); true }

                match key.cmp(&node.key) {
                    Less => node.left.insert(key, val),
                    Equal => node.val = val,
                    Greater => node.right.insert(key, val),
                }

                proof_assert! { node.left.ord_invariant() }
                proof_assert! { node.right.ord_invariant() }
                proof_assert! { node.ord_invariant() }

                if node.right.is_red() && !node.left.is_red() {
                    node.rotate_left();
                }

                if node.left.is_red() && !node.left.node.as_ref().unwrap().left.is_red() {
                    node.rotate_right();
                }

                if node.left.is_red() && node.right.is_red() {
                    node.flip_color();
                    match &mut**node {
                        Node { left: Tree { node: Some(l) },
                               right: Tree { node: Some(r) }, .. } =>
                        {
                            l.flip_color();
                            r.flip_color()
                        },
                        _ => panic!()
                    }
                }
                proof_assert! { node.ord_invariant() }
            }
        }
    }

    fn get(&self, key: &K) -> Option<&V> where K: Ord {
        match &self.node {
            None => None,
            Some(node) => {
                match key.cmp(&node.key) {
                    Less => node.left.get(key),
                    Equal => Some(&node.val),
                    Greater => node.right.get(key)
                }
            }
        }
    }

    fn get_mut(&mut self, key: &K) -> Option<&mut V> where K: Ord {
        match &mut self.node {
            None => None,
            Some(node) => {
                match key.cmp(&node.key) {
                    Less => node.left.get_mut(key),
                    Equal => Some(&mut node.val),
                    Greater => node.right.get_mut(key)
                }
            }
        }
    }

    #[predicate]
    fn ord_invariant(self) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => true,
                Tree { node: Some(node) } => {
                    let Node { left, color, key, val, right } = *node;
                    node.ord_invariant_here() &&
                    left.ord_invariant() && right.ord_invariant()
                }
            }
        }
    }
}

impl<K, V> Tree<K, V> {
    #[ensures(result === true ==>
              exists<node: Box<Node<K, V>>> self.node === Some(node) && node.color === Red)]
    #[ensures(result === false && !(self.node === None) ==>
              exists<node: Box<Node<K, V>>> self.node === Some(node) && node.color === Black)]
    fn is_red(&self) -> bool {
        match self.node {
            Some(box Node{color: Red, ..}) => true,
            _ => false
        }
    }
}

impl<K: Model, V> Node<K, V> {
    #[logic]
    #[ensures(
        (@self).get(key0) ===
            match (@self.right).get(key0) {
                Some(v) => Some(v),
                None =>
                    if @self.key === key0 {
                        Some(self.val)
                    } else {
                        (@self.left).get(key0)
                    }
            })]
    fn model_left_right(self, key0: K::ModelTy) {
        pearlite! { self.right.model_acc_model((@self.left).set(@self.key, Some(self.val)), key0) }
    }

    #[logic]
    #[requires(self.left === o.left)]
    #[requires(self.right === o.right)]
    #[requires(self.key === o.key)]
    #[requires(self.val === o.val)]
    #[ensures(@self === @o)]
    fn model_color(self, o: Self) { }
}

impl<K: Model, V> Tree<K, V> {
    #[logic]
    fn model_acc(self, accu: <Self as Model>::ModelTy) -> <Self as Model>::ModelTy
    {
        pearlite! {
            match self {
                Tree { node: None } => accu,
                Tree { node: Some(node) } => {
                    let Node { left, color, key, val, right } = *node;
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(@key, Some(val));
                    right.model_acc(accu2)
                }
            }
        }
    }

    #[logic]
    #[ensures(
        self.model_acc(accu).get(key0) ===
            match (@self).get(key0) {
                Some(val) => Some(val),
                None => accu.get(key0)
            })]
    fn model_acc_model(self, accu: <Self as Model>::ModelTy, key0: K::ModelTy)
    {
        pearlite! {
            match self {
                Tree { node: None } => (),
                Tree { node: Some(node) } => {
                    let Node { left, color, key, val, right } = *node;
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(@key, Some(val));
                    right.model_acc_model(accu2, key0);

                    let accu1_0 = @left;
                    let accu2_0 = accu1_0.set(@key, Some(node.val));
                    right.model_acc_model(accu2_0, key0);

                    left.model_acc_model(accu, key0)
                }
            }
        }
    }

    #[logic]
    #[requires(self.node === None)]
    #[ensures((@self).get(key0) === None)]
    fn model_leaf(self, key0: K::ModelTy) { }
}

impl<K: Model, V> Model for Node<K, V>{
    type ModelTy = Mapping<K::ModelTy, Option<V>>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        pearlite! {
            self.right.model_acc(self.left.model().set(@self.key, Some(self.val)))
        }
    }
}

impl<K: Model, V> Model for Tree<K, V> {
    type ModelTy = Mapping<K::ModelTy, Option<V>>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        pearlite! { self.model_acc(Mapping::cst(None)) }
    }
}
