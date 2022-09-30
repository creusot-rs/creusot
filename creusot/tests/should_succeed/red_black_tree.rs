// UNSTABLE
#![feature(box_patterns)]
extern crate creusot_contracts;

use creusot_contracts::{derive::Clone, *};
use std::cmp::{Ord, Ordering::*};

#[derive(Clone, Copy)]
enum Color {
    Red,
    Black,
}
use Color::*;

struct Node<K, V> {
    left: Tree<K, V>,
    color: Color,
    key: K,
    val: V,
    right: Tree<K, V>,
}

pub struct Tree<K, V> {
    node: Option<Box<Node<K, V>>>,
}

/*************  The model of a tree, and the set of its mappings  *************/

impl<K: DeepModel, V> Tree<K, V> {
    #[predicate]
    fn has_mapping(self, k: K::DeepModelTy, v: V) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => false,
                Tree { node: Some(box Node { left, key, val, right, .. }) } =>
                    left.has_mapping(k, v) || right.has_mapping(k, v) || k == key.deep_model() && v == val
            }
        }
    }

    #[predicate]
    fn same_mappings(self, o: Self) -> bool {
        pearlite! {
            forall<k: K::DeepModelTy, v: V> self.has_mapping(k, v) == o.has_mapping(k, v)
        }
    }

    #[logic]
    fn model_acc(self, accu: <Self as ShallowModel>::ShallowModelTy) -> <Self as ShallowModel>::ShallowModelTy {
        pearlite! {
            match self {
                Tree { node: None } => accu,
                Tree { node: Some(box Node { left, key, val, right, .. }) } => {
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(key.deep_model(), Some(val));
                    right.model_acc(accu2)
                }
            }
        }
    }

    #[logic]
    #[ensures(self.model_acc(accu).get(k) == accu.get(k) ||
              exists<v: V> self.model_acc(accu).get(k) == Some(v) && self.has_mapping(k, v))]
    fn model_acc_has_mapping(self, accu: <Self as ShallowModel>::ShallowModelTy, k: K::DeepModelTy) {
        pearlite! {
            match self {
                Tree { node: None } => (),
                Tree { node: Some(box Node { left, key, val, right, .. }) } => {
                    left.model_acc_has_mapping(accu, k);
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(key.deep_model(), Some(val));
                    right.model_acc_has_mapping(accu2, k)
                }
            }
        }
    }

    #[logic]
    #[requires(self.bst_invariant())]
    #[ensures(forall<v: V> self.has_mapping(k, v) ==> self.model_acc(accu).get(k) == Some(v))]
    fn has_mapping_model_acc(self, accu: <Self as ShallowModel>::ShallowModelTy, k: K::DeepModelTy)
    where
        K::DeepModelTy: OrdLogic,
    {
        pearlite! {
            match self {
                Tree { node: None } => (),
                Tree { node: Some(box Node { left, key, val, right, .. }) } => {
                    left.has_mapping_model_acc(accu, k);
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(key.deep_model(), Some(val));
                    right.has_mapping_model_acc(accu2, k);
                    right.model_acc_has_mapping(accu2, k)
                }
            }
        }
    }

    #[logic]
    #[requires(self.bst_invariant())]
    #[ensures(forall<v: V> self.has_mapping(k, v) == ((@self).get(k) == Some(v)))]
    fn has_mapping_model(self, k: K::DeepModelTy)
    where
        K::DeepModelTy: OrdLogic,
    {
        pearlite! { {
            self.model_acc_has_mapping(Mapping::cst(None), k);
            self.has_mapping_model_acc(Mapping::cst(None), k)
        } }
    }

    #[logic]
    #[requires(self.bst_invariant())]
    #[requires(self.has_mapping(k, v1))]
    #[requires(self.has_mapping(k, v2))]
    #[ensures(v1 == v2)]
    fn has_mapping_inj(self, k: K::DeepModelTy, v1: V, v2: V)
    where
        K::DeepModelTy: OrdLogic,
    {
        pearlite! { {
            self.has_mapping_model(k);
            match (@self).get(k) { None => (), Some(_v) => () }
        } }
    }
}

impl<K: DeepModel, V> Node<K, V> {
    #[predicate]
    #[ensures(forall<node: Box<Node<K, V>>>
              self == *node ==> result == Tree{ node: Some(node) }.has_mapping(k, v))]
    fn has_mapping(self, k: K::DeepModelTy, v: V) -> bool {
        pearlite! {
            self.left.has_mapping(k, v) || self.right.has_mapping(k, v) ||
                k == self.key.deep_model() && v == self.val
        }
    }

    #[predicate]
    fn same_mappings(self, o: Self) -> bool {
        pearlite! {
            forall<k: K::DeepModelTy, v: V> self.has_mapping(k, v) == o.has_mapping(k, v)
        }
    }
}

impl<K: DeepModel, V> ShallowModel for Node<K, V> {
    type ShallowModelTy = Mapping<K::DeepModelTy, Option<V>>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! {
            self.right.model_acc(self.left.shallow_model().set(self.key.deep_model(), Some(self.val)))
        }
    }
}

impl<K: DeepModel, V> ShallowModel for Tree<K, V> {
    type ShallowModelTy = Mapping<K::DeepModelTy, Option<V>>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.model_acc(Mapping::cst(None)) }
    }
}

/*******************************  The BST invariant ***************************/

impl<K: DeepModel, V> Node<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    fn bst_invariant_here(self) -> bool {
        pearlite! {
            (forall<k: K::DeepModelTy, v: V> self.left.has_mapping(k, v) ==> k < self.key.deep_model()) &&
            (forall<k: K::DeepModelTy, v: V> self.right.has_mapping(k, v) ==> self.key.deep_model() < k)
        }
    }

    #[predicate]
    fn bst_invariant(self) -> bool {
        pearlite! {
            self.bst_invariant_here() && self.left.bst_invariant() && self.right.bst_invariant()
        }
    }
}

impl<K: DeepModel, V> Tree<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    fn bst_invariant(self) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => true,
                Tree { node: Some(box node) } => {
                    let Node { left, right, .. } = node;
                    node.bst_invariant_here() && left.bst_invariant() && right.bst_invariant()
                }
            }
        }
    }
}

/******************  The color invariant, and color patterns ****************/

trait CP<K, V> {
    #[predicate]
    fn match_t(self, tree: Tree<K, V>) -> bool;

    #[predicate]
    fn match_n(self, node: Node<K, V>) -> bool;
}

struct CPL(Color);
impl<K, V> CP<K, V> for CPL {
    #[predicate]
    #[ensures(self.0 == Red ==>
              result ==
              exists<node: Box<Node<K, V>>> tree.node == Some(node) &&
                CPL(Red).match_n(*node))]
    #[ensures(self.0 == Red ==>
              result ==
              (tree.node != None &&
               forall<node: Box<Node<K, V>>> tree.node == Some(node) ==>
               CPL(Red).match_n(*node)))]
    #[ensures(self.0 == Black ==>
              result ==
              (tree.node == None ||
               exists<node: Box<Node<K, V>>> tree.node == Some(node) &&
                CPL(Black).match_n(*node)))]
    #[ensures(self.0 == Black ==>
              result ==
              (forall<node: Box<Node<K, V>>> tree.node == Some(node) ==>
               CPL(Black).match_n(*node)))]
    fn match_t(self, tree: Tree<K, V>) -> bool {
        pearlite! {
            tree.color() == self.0 && tree.color_invariant()
        }
    }

    #[predicate]
    fn match_n(self, node: Node<K, V>) -> bool {
        pearlite! {
            node.color == self.0 && node.color_invariant()
        }
    }
}

struct CPN<L, R>(Color, L, R);
impl<K, V, L: CP<K, V>, R: CP<K, V>> CP<K, V> for CPN<L, R> {
    #[predicate]
    fn match_t(self, tree: Tree<K, V>) -> bool {
        pearlite! {
            exists<node: Box<Node<K, V>>> tree.node == Some(node) &&
                self.match_n(*node)
        }
    }

    #[predicate]
    fn match_n(self, node: Node<K, V>) -> bool {
        pearlite! {
            node.color == self.0 && self.1.match_t(node.left) && self.2.match_t(node.right)
        }
    }
}

impl<K, V> Tree<K, V> {
    #[logic]
    fn color(self) -> Color {
        pearlite! {
            match self.node {
                Some(box Node { color, .. }) => color,
                _ => Black,
            }
        }
    }

    #[predicate]
    fn color_invariant(self) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => true,
                Tree { node: Some(box node) } => {
                    let Node { left, right, .. } = node;
                    node.color_invariant_here() && left.color_invariant() && right.color_invariant()
                }
            }
        }
    }
}

impl<K, V> Node<K, V> {
    #[predicate]
    fn color_invariant_here(self) -> bool {
        pearlite! { self.right.color() == Black && (self.color == Black || self.left.color() == Black) }
    }

    #[predicate]
    fn color_invariant(self) -> bool {
        pearlite! { self.color_invariant_here() && self.left.color_invariant() && self.right.color_invariant() }
    }
}

/*****************************  The height invariant  *************************/

impl<K, V> Tree<K, V> {
    #[logic]
    #[ensures(result >= 0)]
    fn height(self) -> Int {
        pearlite! {
            match self {
                Tree { node: None } => 0,
                Tree { node: Some(box Node { left, color, .. })} => {
                    match color {
                        Red => left.height(),
                        Black => left.height()+1
                    }
                }
            }
        }
    }

    #[predicate]
    fn height_invariant(self) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => true,
                Tree { node: Some(box node) } => {
                    let Node { left, right, .. } = node;
                    node.height_invariant_here() && left.height_invariant() && right.height_invariant()
                }
            }
        }
    }
}

impl<K, V> Node<K, V> {
    #[logic]
    #[ensures(forall<node: Box<Node<K, V>>>
              self == *node ==> result == Tree{ node: Some(node) }.height())]
    fn height(self) -> Int {
        pearlite! {
            match self.color {
                Red => self.left.height(),
                Black => self.left.height()+1
            }
        }
    }

    #[predicate]
    fn height_invariant_here(self) -> bool {
        pearlite! { self.left.height() == self.right.height() }
    }

    #[predicate]
    fn height_invariant(self) -> bool {
        pearlite! { self.height_invariant_here() && self.left.height_invariant() && self.right.height_invariant() }
    }
}

/*************************  Conjunction of invariants  ************************/

impl<K: DeepModel, V> Tree<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    pub fn internal_invariant(self) -> bool {
        pearlite! {
            self.bst_invariant() && self.height_invariant()
        }
    }

    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            self.internal_invariant() && self.color_invariant() && self.color() == Black
        }
    }
}

impl<K: DeepModel, V> Node<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    pub fn internal_invariant(self) -> bool {
        pearlite! {
            self.bst_invariant() && self.height_invariant()
        }
    }
}

/*************************  Code of the data structure  ***********************/

impl<K: DeepModel, V> Tree<K, V> {
    #[ensures(result == (self.color() == Red))]
    fn is_red(&self) -> bool {
        match self.node {
            Some(box Node { color: Red, .. }) => true,
            _ => false,
        }
    }
}

impl<K: DeepModel, V> Node<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[requires((*self).internal_invariant())]
    #[requires((*self).left.color() == Red)]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures((^self).key.deep_model() < (*self).key.deep_model())]
    #[ensures((^self).right.color() == Red)]
    #[ensures((^self).color == (*self).color)]
    #[ensures(exists<l: Box<Self>, r: Box<Self>>
              (*self).left.node == Some(l) && (^self).right.node == Some(r) &&
              ((^self).left, r.left, r.right) == (l.left, l.right, (*self).right) &&
              r.key == (*self).key)]
    fn rotate_right(&mut self) {
        let old_self = ghost! { self };

        //     self
        //    /    \
        //   x      c
        //  / \
        // a   b
        // Rip out the left subtree
        let mut x = std::mem::take(&mut self.left.node).unwrap();

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
        std::mem::swap(&mut self.color, &mut x.color);
        //   self
        //  /
        // a      x
        //       / \
        //      b   c
        proof_assert! { old_self.left.has_mapping((*self).key.deep_model(), (*self).val) }
        proof_assert! { forall<k: K::DeepModelTy, v: V> x.left.has_mapping(k, v) ==> old_self.left.has_mapping(k, v) }
        self.right = Tree { node: Some(x) };
        //   self
        //  /    \
        // a      x
        //       / \
        //      b   c
    }

    #[requires((*self).internal_invariant())]
    #[requires((*self).right.color() == Red)]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures((*self).key.deep_model() < (^self).key.deep_model())]
    #[ensures((^self).left.color() == Red)]
    #[ensures((^self).color == (*self).color)]
    #[ensures(exists<l: Box<Self>, r: Box<Self>>
              (*self).right.node == Some(r) && (^self).left.node == Some(l) &&
              (l.left, l.right, (^self).right) == ((*self).left, r.left, r.right) &&
              l.key == (*self).key)]
    fn rotate_left(&mut self) {
        let old_self = ghost! { self };
        let mut x = std::mem::take(&mut self.right.node).unwrap();
        std::mem::swap(&mut self.right, &mut x.left);
        std::mem::swap(self, &mut x);
        std::mem::swap(&mut self.color, &mut x.color);
        proof_assert! { old_self.right.has_mapping((*self).key.deep_model(), (*self).val) }
        proof_assert! { forall<k: K::DeepModelTy, v: V> x.right.has_mapping(k, v) ==> old_self.right.has_mapping(k, v) }
        self.left = Tree { node: Some(x) };
    }

    #[requires((*self).internal_invariant())]
    #[requires((*self).left.node != None)]
    #[requires((*self).right.node != None)]
    #[requires((*self).left.color() == (*self).right.color())]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((*self).key == (^self).key)]
    #[ensures(exists<l1: Box<Self>, l2: Box<Self>> (*self).left.node == Some(l1) && (^self).left.node == Some(l2) &&
              l1.left == l2.left && l1.right == l2.right && l1.key == l2.key &&
              (*self).color == l2.color && (^self).color == l1.color)]
    #[ensures(exists<r1: Box<Self>, r2: Box<Self>> (*self).right.node == Some(r1) && (^self).right.node == Some(r2) &&
              r1.left == r2.left && r1.right == r2.right && r1.key == r2.key &&
              (*self).color == r2.color && (^self).color == r1.color && r1.key == r2.key)]
    fn flip_colors(&mut self) {
        self.left.node.as_mut().unwrap().color = self.color;
        std::mem::swap(&mut self.color, &mut self.right.node.as_mut().unwrap().color);
    }

    #[requires((*self).internal_invariant())]
    #[requires((*self).color == Red && (*self).left.color() == Red ==>
               (*self).left.color_invariant())]
    #[requires((*self).color == Red && (*self).right.color() == Red ==>
               (*self).right.color_invariant())]
    #[requires((*self).color == Red && (*self).right.color() == Red && (*self).left.color() == Red ==> false)]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures((*self).left.color_invariant() && (*self).right.color() == Black ==>
              (*self) == (^self))]
    #[ensures(CPN(Black, CPN(Red, CPL(Red), CPL(Black)), CPL(Black)).match_n(*self) ==>
              CPL(Red).match_n(^self))]
    #[ensures(CPN(Black, CPL(Black), CPL(Red)).match_n(*self) ==>
              CPN(Black, CPL(Red), CPL(Black)).match_n(^self))]
    #[ensures(CPN(Red, CPL(Black), CPL(Red)).match_n(*self) ==>
              CPN(Red, CPL(Red), CPL(Black)).match_n(^self))]
    #[ensures(CPN(Black, CPL(Red), CPL(Red)).match_n(*self) ==>
              CPL(Red).match_n(^self))]
    fn balance(&mut self) {
        if self.right.is_red() && !self.left.is_red() {
            self.rotate_left();
        }

        if self.left.is_red() && self.left.node.as_ref().unwrap().left.is_red() {
            self.rotate_right();
        }

        if self.left.is_red() && self.right.is_red() {
            self.flip_colors();
        }
    }

    #[requires((*self).right.node != None)]
    #[requires((*self).internal_invariant())]
    #[requires(CPN(Red, CPN(Black, CPL(Black), CPL(Black)), CPL(Black)).match_n(*self))]
    #[ensures((*result).internal_invariant())]
    #[ensures((^result).internal_invariant() && (*result).height() == (^result).height()
              && (forall<k: K::DeepModelTy, v: V> (^result).has_mapping(k, v) ==> (*result).has_mapping(k, v))
              ==> (^self).internal_invariant())]
    #[ensures((*result).height() == (^result).height() ==> (*self).height() == (^self).height())]
    #[ensures((*self).key == (*result).key)]
    #[ensures(forall<k: K::DeepModelTy, v: V> (*result).has_mapping(k, v) ==> (*self).has_mapping(k, v))]
    #[ensures(forall<k: K::DeepModelTy, v: V> (*self).has_mapping(k, v) && k <= (*self).key.deep_model()
              ==> (*result).has_mapping(k, v))]
    #[ensures(forall<k: K::DeepModelTy, v: V> (^self).has_mapping(k, v) ==
              ((^result).has_mapping(k, v) || ((*self).has_mapping(k, v) && !(*result).has_mapping(k, v))))]
    #[ensures(CPN(Black, CPL(Red), CPL(Black)).match_n(*result) ||
              CPN(Black, CPL(Red), CPL(Red)).match_n(*result))]
    #[ensures((^result).color_invariant() && ((*result).right.color() == Black ==> (^result).color == Black)
              ==> (^self).color_invariant())]
    fn move_red_left(&mut self) -> &mut Self {
        self.flip_colors();
        if self.right.node.as_mut().unwrap().left.is_red() {
            self.right.node.as_mut().unwrap().rotate_right();
            self.rotate_left();
            self.flip_colors();
            return self.left.node.as_mut().unwrap();
        }
        return self;
    }

    #[requires((*self).left.node != None)]
    #[requires((*self).internal_invariant())]
    #[requires(CPN(Red, CPL(Black), CPN(Black, CPL(Black), CPL(Black))).match_n(*self))]
    #[ensures((*result).internal_invariant())]
    #[ensures((^result).internal_invariant() && (*result).height() == (^result).height()
              && (forall<k: K::DeepModelTy, v: V> (^result).has_mapping(k, v) ==> (*result).has_mapping(k, v))
              ==> (^self).internal_invariant())]
    #[ensures((*result).height() == (^result).height() ==> (*self).height() == (^self).height())]
    #[ensures((*result).key == (*self).key)]
    #[ensures(forall<k: K::DeepModelTy, v: V> (*result).has_mapping(k, v) ==> (*self).has_mapping(k, v))]
    #[ensures(forall<k: K::DeepModelTy, v: V> (*self).has_mapping(k, v) && (*self).key.deep_model() <= k
              ==> (*result).has_mapping(k, v))]
    #[ensures(forall<k: K::DeepModelTy, v: V> (^self).has_mapping(k, v) ==
              ((^result).has_mapping(k, v) || ((*self).has_mapping(k, v) && !(*result).has_mapping(k, v))))]
    #[ensures(CPN(Black, CPL(Black), CPL(Red)).match_n(*result) ||
              CPN(Black, CPL(Red), CPL(Red)).match_n(*result))]
    #[ensures((^result).color_invariant() && ((*result).left.color() == Black ==> (^result).color == Black)
              ==> (^self).color_invariant())]
    fn move_red_right(&mut self) -> &mut Self {
        self.flip_colors();
        if self.left.node.as_mut().unwrap().left.is_red() {
            self.rotate_right();
            self.flip_colors();
            return self.right.node.as_mut().unwrap();
        }
        return self;
    }
}

impl<K: DeepModel + Ord, V> Tree<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[ensures(@result == Mapping::cst(None))]
    #[ensures(result.invariant())]
    pub fn new() -> Tree<K, V> {
        Tree { node: None }
    }

    #[requires((*self).internal_invariant())]
    #[requires((*self).color_invariant())]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures(CPN(Red, CPL(Red), CPL(Black)).match_t(^self) && (*self).color() == Red ||
              (^self).color_invariant())]
    #[ensures((^self).has_mapping(key.deep_model(), val))]
    #[ensures(forall<k: K::DeepModelTy, v: V> k == key.deep_model() || (*self).has_mapping(k, v) == (^self).has_mapping(k, v))]
    fn insert_rec(&mut self, key: K, val: V) {
        if let Some(node) = &mut self.node {
            match key.cmp(&node.key) {
                Less => node.left.insert_rec(key, val),
                Equal => {
                    node.val = val;
                    return;
                }
                Greater => node.right.insert_rec(key, val),
            }
            node.balance();
        } else {
            self.node = Some(Box::new(Node {
                left: Tree { node: None },
                color: Red,
                key,
                val,
                right: Tree { node: None },
            }));
            return; // FIXME: not necessary, but Creusot crashes if we remove this return.
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(@^self == (@self).set(key.deep_model(), Some(val)))]
    pub fn insert(&mut self, key: K, val: V) {
        self.insert_rec(key, val);
        self.node.as_mut().unwrap().color = Black;
        ghost! { Self::has_mapping_model };
    }

    #[requires((*self).internal_invariant())]
    #[requires(CPL(Red).match_t(*self) ||
               CPN(Black, CPL(Red), CPL(Black)).match_t(*self))]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures((*self).has_mapping(result.0.deep_model(), result.1))]
    #[ensures(forall<k: K::DeepModelTy, v: V> (*self).has_mapping(k, v) ==> k <= result.0.deep_model())]
    #[ensures(forall<k: K::DeepModelTy, v: V> (^self).has_mapping(k, v) ==
              (result.0.deep_model() != k && (*self).has_mapping(k, v)))]
    #[ensures((^self).color_invariant())]
    #[ensures((*self).color() == Black ==> (^self).color() == Black)]
    fn delete_max_rec(&mut self) -> (K, V) {
        let mut node = self.node.as_mut().unwrap().as_mut();
        if node.left.is_red() {
            node.rotate_right()
        }
        if let None = node.right.node {
            let node = std::mem::take(&mut self.node).unwrap();
            return (node.key, node.val);
        }
        if !node.right.is_red() && !node.right.node.as_ref().unwrap().left.is_red() {
            node = node.move_red_right();
        }
        let r = node.right.delete_max_rec();
        node.balance();
        r
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(result == None ==> @^self == @self && @self == Mapping::cst(None))]
    #[ensures(forall<k: K, v: V> result == Some((k, v)) ==>
              (@self).get(k.deep_model()) == Some(v) &&
              (forall<k2: K::DeepModelTy> (@self).get(k2) == None || k2 <= k.deep_model()) &&
              @^self == (@self).set(k.deep_model(), None))]
    pub fn delete_max(&mut self) -> Option<(K, V)> {
        let old_self = ghost! { self };
        if let Some(node) = &mut self.node {
            if !node.left.is_red() {
                node.color = Red;
            }
        } else {
            return None;
        }
        proof_assert! { old_self.same_mappings(*self) }
        let r = self.delete_max_rec();
        if self.is_red() {
            self.node.as_mut().unwrap().color = Black;
        }
        ghost! { Self::has_mapping_model };
        Some(r)
    }

    #[requires((*self).internal_invariant())]
    #[requires(CPL(Red).match_t(*self) ||
               CPN(Black, CPL(Red), CPL(Black)).match_t(*self))]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures((*self).has_mapping(result.0.deep_model(), result.1))]
    #[ensures(forall<k: K::DeepModelTy, v: V> (*self).has_mapping(k, v) ==> result.0.deep_model() <= k)]
    #[ensures(forall<k: K::DeepModelTy, v: V> (^self).has_mapping(k, v) ==
              (result.0.deep_model() != k && (*self).has_mapping(k, v)))]
    #[ensures((^self).color_invariant())]
    #[ensures((*self).color() == Black ==> (^self).color() == Black)]
    fn delete_min_rec(&mut self) -> (K, V) {
        let mut node = self.node.as_mut().unwrap().as_mut();
        if let None = node.left.node {
            let node = std::mem::take(&mut self.node).unwrap();
            return (node.key, node.val);
        }
        if !node.left.is_red() && !node.left.node.as_ref().unwrap().left.is_red() {
            node = node.move_red_left();
        }
        let r = node.left.delete_min_rec();
        node.balance();
        r
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(result == None ==> @^self == @self && @self == Mapping::cst(None))]
    #[ensures(forall<k: K, v: V> result == Some((k, v)) ==>
              (@self).get(k.deep_model()) == Some(v) &&
              (forall<k2: K::DeepModelTy> (@self).get(k2) == None || k.deep_model() <= k2) &&
              @^self == (@self).set(k.deep_model(), None))]
    pub fn delete_min(&mut self) -> Option<(K, V)> {
        let old_self = ghost! { self };
        if let Some(node) = &mut self.node {
            if !node.left.is_red() {
                node.color = Red;
            }
        } else {
            return None;
        }
        proof_assert! { old_self.same_mappings(*self) }
        let r = self.delete_min_rec();
        if self.is_red() {
            self.node.as_mut().unwrap().color = Black;
        }
        ghost! { Self::has_mapping_model };
        Some(r)
    }

    #[requires((*self).internal_invariant())]
    #[requires(CPL(Red).match_t(*self) ||
               CPN(Black, CPL(Red), CPL(Black)).match_t(*self))]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures(forall<v: V> result == None ==> !(*self).has_mapping(key.deep_model(), v))]
    #[ensures(forall<k: K, v: V> result == Some((k, v)) ==>
              key.deep_model() == k.deep_model() && (*self).has_mapping(k.deep_model(), v))]
    #[ensures(forall<k: K::DeepModelTy, v: V> (^self).has_mapping(k, v) == (key.deep_model() != k && (*self).has_mapping(k, v)))]
    #[ensures((^self).color_invariant())]
    #[ensures((*self).color() == Black ==> (^self).color() == Black)]
    fn delete_rec(&mut self, key: &K) -> Option<(K, V)> {
        let r;
        let mut node = self.node.as_mut().unwrap().as_mut();
        match key.cmp(&node.key) {
            Less => {
                if node.left.node.is_none() {
                    return None;
                }
                if !node.left.is_red() && !node.left.node.as_ref().unwrap().left.is_red() {
                    node = node.move_red_left();
                }
                r = node.left.delete_rec(key)
            }
            ord => {
                if node.left.is_red() {
                    node.rotate_right();
                    r = node.right.delete_rec(key)
                } else {
                    if node.right.node.is_none() {
                        if let Greater = ord {
                            return None;
                        }
                        let node = std::mem::take(&mut self.node).unwrap();
                        return Some((node.key, node.val));
                    }
                    if !node.right.node.as_ref().unwrap().left.is_red() {
                        node = node.move_red_right();
                    }
                    if let Equal = ord {
                        let mut kv = node.right.delete_min_rec();
                        ghost! { Self::has_mapping_inj };
                        std::mem::swap(&mut node.key, &mut kv.0);
                        std::mem::swap(&mut node.val, &mut kv.1);
                        r = Some(kv)
                    } else {
                        r = node.right.delete_rec(key)
                    }
                }
            }
        }
        node.balance();
        r
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((result == None) == ((@self).get(key.deep_model()) == None))]
    #[ensures(forall<k: K, v: V> result == Some((k, v)) && k.deep_model() == key.deep_model() ==>
              (@self).get(key.deep_model()) == Some(v))]
    #[ensures(@^self == (@self).set(key.deep_model(), None))]
    pub fn delete(&mut self, key: &K) -> Option<(K, V)> {
        ghost! { Self::has_mapping_model };

        let old_self = ghost! { self };
        if let Some(node) = &mut self.node {
            if !node.left.is_red() {
                node.color = Red;
            }
        } else {
            return None;
        }
        let r = self.delete_rec(key);
        proof_assert! { @self == (@old_self).set(key.deep_model(), None) }
        if self.is_red() {
            self.node.as_mut().unwrap().color = Black;
        }
        ghost! { match r { None => (), Some(_) => () }};
        r
    }

    #[requires((*self).invariant())]
    #[ensures(forall<v: &V> result == Some(v) ==> (@self).get(key.deep_model()) == Some(*v))]
    #[ensures(result == None ==> (@self).get(key.deep_model()) == None)]
    pub fn get(&self, key: &K) -> Option<&V> {
        ghost! { Self::has_mapping_model };

        let mut tree = self;
        #[invariant(bst_inv, (*tree).bst_invariant())]
        #[invariant(has_mapping, forall<v: V> (*self).has_mapping(key.deep_model(), v) == (*tree).has_mapping(key.deep_model(), v))]
        while let Some(node) = &tree.node {
            match key.cmp(&node.key) {
                Less => tree = &node.left,
                Equal => return Some(&node.val),
                Greater => tree = &node.right,
            }
        }
        return None;
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(forall<v: &mut V> result == Some(v) ==>
              (@self).get(key.deep_model()) == Some(*v) && @^self == (@self).set(key.deep_model(), Some(^v)))]
    #[ensures(result == None ==> (@self).get(key.deep_model()) == None && (@^self).get(key.deep_model()) == None)]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        ghost! { Self::has_mapping_model };

        let old_self = ghost! { self };
        let mut tree = self;

        #[invariant(bst_inv, (*tree).bst_invariant())]
        #[invariant(height_inv, (*tree).height_invariant())]
        #[invariant(color_inv, (*tree).color_invariant())]
        #[invariant(mapping_prof_key, forall<v: V> (^tree).has_mapping(key.deep_model(), v) == (^*old_self).has_mapping(key.deep_model(), v))]
        #[invariant(mapping_cur_key, forall<v: V> (*tree).has_mapping(key.deep_model(), v) == (**old_self).has_mapping(key.deep_model(), v))]
        #[invariant(bst_inv_proph, (forall<k: K::DeepModelTy, v: V> k == key.deep_model() || (*tree).has_mapping(k, v) == (^tree).has_mapping(k, v))
                    ==> (^tree).bst_invariant() ==> (^*old_self).bst_invariant())]
        #[invariant(height_inv_proph,
                    (*tree).height() == (^tree).height() && (^tree).height_invariant() ==>
                    (^*old_self).height_invariant())]
        #[invariant(color_inv_proph, CPL((*tree).color()).match_t(^tree) ==> CPL(Black).match_t(^*old_self))]
        #[invariant(mapping_proph,
                    forall<k: K::DeepModelTy, v: V> (*tree).has_mapping(k, v) == (^tree).has_mapping(k, v) ==>
                    (**old_self).has_mapping(k, v) == (^*old_self).has_mapping(k, v))]
        while let Some(node) = &mut tree.node {
            match key.cmp(&node.key) {
                Less => tree = &mut node.left,
                Equal => return Some(&mut node.val),
                Greater => tree = &mut node.right,
            }
        }
        return None;
    }
}
