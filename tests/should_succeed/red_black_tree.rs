// TIME 5
#![feature(box_patterns)]
extern crate creusot_contracts;

use creusot_contracts::{
    Clone,
    invariant::{Invariant, inv},
    logic::Mapping,
    *,
};
use std::cmp::Ordering::*;

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

struct Tree<K, V> {
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
    fn model_acc(self, accu: <Self as View>::ViewTy) -> <Self as View>::ViewTy {
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
    fn model_acc_has_mapping(self, accu: <Self as View>::ViewTy, k: K::DeepModelTy) {
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
    fn has_mapping_model_acc(self, accu: <Self as View>::ViewTy, k: K::DeepModelTy)
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
    #[ensures(forall<v: V> self.has_mapping(k, v) == (self@.get(k) == Some(v)))]
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
            match self@.get(k) { None => (), Some(_v) => () }
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

impl<K: DeepModel, V> View for Node<K, V> {
    type ViewTy = Mapping<K::DeepModelTy, Option<V>>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        pearlite! {
            self.right.model_acc(self.left.view().set(self.key.deep_model(), Some(self.val)))
        }
    }
}

impl<K: DeepModel, V> View for Tree<K, V> {
    type ViewTy = Mapping<K::DeepModelTy, Option<V>>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        pearlite! { self.model_acc(Mapping::cst(None)) }
    }
}

impl<K: DeepModel, V> Resolve for Tree<K, V> {
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! {
            forall<k: _, v: V> self.has_mapping(k, v) ==> resolve(&v)
        }
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<K: DeepModel, V> Resolve for Node<K, V> {
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! {
            forall<k: _, v: V> self.has_mapping(k, v) ==> resolve(&v)
        }
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
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

enum CP {
    CPL(Color),
    CPN(Color, Box<CP>, Box<CP>),
}
use CP::*;

#[logic]
fn cpn(c: Color, l: CP, r: CP) -> CP {
    pearlite! { CPN(c, Box::new(l), Box::new(r)) }
}

impl CP {
    #[predicate]
    fn match_t<K, V>(self, tree: Tree<K, V>) -> bool {
        pearlite! {
            match self {
                CPL(color) => tree.color() == color && tree.color_invariant(),
                CPN(color, box l, box r) =>
                    exists<node: Box<Node<K, V>>> tree.node == Some(node) &&
                    node.color == color && l.match_t(node.left) && r.match_t(node.right)
            }
        }
    }

    #[predicate]
    fn match_n<K, V>(self, node: Node<K, V>) -> bool {
        pearlite! {
            match self {
                CPL(color) => node.color == color && node.color_invariant(),
                CPN(color, box l, box r) => node.color == color && l.match_t(node.left) && r.match_t(node.right)
            }
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

impl<K: DeepModel, V> Tree<K, V> {
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

impl<K: DeepModel, V> Node<K, V> {
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
    fn internal_invariant(self) -> bool {
        pearlite! {
            self.bst_invariant() && self.height_invariant()
        }
    }
}

impl<K: DeepModel, V> Node<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    // TODO
    // This might be made a proper type invariant, but move_red_left/move_red_right need to be
    // rewritten, perhaps by taking a continuation as closure in parameter.
    fn internal_invariant(self) -> bool {
        pearlite! {
            self.bst_invariant() && self.height_invariant()
        }
    }
}

/*************************  Internal code of the data structure  ***********************/

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
        let old_self = snapshot! { self };

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
        let old_self = snapshot! { self };
        let mut x = std::mem::take(&mut self.right.node).unwrap();
        std::mem::swap(&mut self.right, &mut x.left);
        std::mem::swap(self, &mut x);
        std::mem::swap(&mut self.color, &mut x.color);
        proof_assert! { old_self.right.has_mapping((*self).key.deep_model(), (*self).val) }
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
    #[ensures(cpn(Black, cpn(Red, CPL(Red), CPL(Black)), CPL(Black)).match_n(*self) ==>
              CPL(Red).match_n(^self))]
    #[ensures(cpn(Black, CPL(Black), CPL(Red)).match_n(*self) ==>
              cpn(Black, CPL(Red), CPL(Black)).match_n(^self))]
    #[ensures(cpn(Red, CPL(Black), CPL(Red)).match_n(*self) ==>
              cpn(Red, CPL(Red), CPL(Black)).match_n(^self))]
    #[ensures(cpn(Black, CPL(Red), CPL(Red)).match_n(*self) ==>
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
    #[requires(cpn(Red, cpn(Black, CPL(Black), CPL(Black)), CPL(Black)).match_n(*self))]
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
    #[ensures(cpn(Black, CPL(Red), CPL(Black)).match_n(*result) ||
              cpn(Black, CPL(Red), CPL(Red)).match_n(*result))]
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
    #[requires(cpn(Red, CPL(Black), cpn(Black, CPL(Black), CPL(Black))).match_n(*self))]
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
    #[ensures(cpn(Black, CPL(Black), CPL(Red)).match_n(*result) ||
              cpn(Black, CPL(Red), CPL(Red)).match_n(*result))]
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
    #[requires((*self).internal_invariant())]
    #[requires((*self).color_invariant())]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures(cpn(Red, CPL(Red), CPL(Black)).match_t(^self) && (*self).color() == Red ||
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

    #[requires((*self).internal_invariant())]
    #[requires(CPL(Red).match_t(*self) ||
               cpn(Black, CPL(Red), CPL(Black)).match_t(*self))]
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

    #[requires((*self).internal_invariant())]
    #[requires(CPL(Red).match_t(*self) ||
               cpn(Black, CPL(Red), CPL(Black)).match_t(*self))]
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

    #[requires((*self).internal_invariant())]
    #[requires(CPL(Red).match_t(*self) ||
               cpn(Black, CPL(Red), CPL(Black)).match_t(*self))]
    #[ensures((^self).internal_invariant())]
    #[ensures((*self).height() == (^self).height())]
    #[ensures(match result {
        None => forall<v: V> !(*self).has_mapping(key.deep_model(), v),
        Some((k, v)) => key.deep_model() == k.deep_model() && (*self).has_mapping(k.deep_model(), v)
    })]
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
                        snapshot! { Self::has_mapping_inj };
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
}

/*************  External interface  *************/

pub struct Map<K, V>(Tree<K, V>);

impl<K: DeepModel, V> View for Map<K, V> {
    type ViewTy = Mapping<K::DeepModelTy, Option<V>>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        pearlite! { self.0@ }
    }
}

impl<K: DeepModel, V> Invariant for Map<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.0.internal_invariant() && self.0.color_invariant() && self.0.color() == Black
        }
    }
}

impl<K: DeepModel, V> Resolve for Map<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        pearlite! { forall<k: K::DeepModelTy> resolve(&self@.get(k)) }
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    #[allow(path_statements)]
    fn resolve_coherence(&self) {
        Tree::<K, V>::has_mapping_model;
    }
}

impl<K: DeepModel + Ord, V> Map<K, V>
where
    K::DeepModelTy: OrdLogic,
{
    #[ensures(result@ == Mapping::cst(None))]
    pub fn new() -> Self {
        Map(Tree { node: None })
    }

    #[ensures((^self)@ == self@.set(key.deep_model(), Some(val)))]
    pub fn insert(&mut self, key: K, val: V) {
        self.0.insert_rec(key, val);
        self.0.node.as_mut().unwrap().color = Black;
        snapshot! { Tree::<K, V>::has_mapping_model };
    }

    #[ensures(match result {
        Some((k, v)) => self@.get(k.deep_model()) == Some(v) &&
            (forall<k2: K::DeepModelTy> self@.get(k2) == None || k2 <= k.deep_model()) &&
            (^self)@ == self@.set(k.deep_model(), None),
        None => (^self)@ == self@ && self@ == Mapping::cst(None)
    })]
    pub fn delete_max(&mut self) -> Option<(K, V)> {
        let old_self = snapshot! { self };
        if let Some(node) = &mut self.0.node {
            if !node.left.is_red() {
                node.color = Red;
            }
        } else {
            return None;
        }
        proof_assert! { old_self.0.same_mappings(self.0) }
        let r = self.0.delete_max_rec();
        if self.0.is_red() {
            self.0.node.as_mut().unwrap().color = Black;
        }
        snapshot! { Tree::<K, V>::has_mapping_model };
        Some(r)
    }

    #[ensures(match result {
        Some((k, v)) =>
            self@.get(k.deep_model()) == Some(v) &&
            (forall<k2: K::DeepModelTy> self@.get(k2) == None || k.deep_model() <= k2) &&
            (^self)@ == self@.set(k.deep_model(), None),
        None => (^self)@ == self@ && self@ == Mapping::cst(None)
    })]
    pub fn delete_min(&mut self) -> Option<(K, V)> {
        snapshot! { Tree::<K, V>::has_mapping_model };

        if let Some(node) = &mut self.0.node {
            if !node.left.is_red() {
                node.color = Red;
            }
        } else {
            return None;
        }
        let r = self.0.delete_min_rec();
        if self.0.is_red() {
            self.0.node.as_mut().unwrap().color = Black;
        }
        Some(r)
    }

    #[ensures(match result {
        Some((k, v)) =>
            k.deep_model() == key.deep_model() && self@.get(key.deep_model()) == Some(v),
        None => self@.get(key.deep_model()) == None
    })]
    #[ensures((^self)@ == self@.set(key.deep_model(), None))]
    pub fn delete(&mut self, key: &K) -> Option<(K, V)> {
        snapshot! { Tree::<K, V>::has_mapping_model };

        if let Some(node) = &mut self.0.node {
            if !node.left.is_red() {
                node.color = Red;
            }
        } else {
            return None;
        }
        let r = self.0.delete_rec(key);
        if self.0.is_red() {
            self.0.node.as_mut().unwrap().color = Black;
        }
        r
    }

    #[ensures(match result {
        Some(v) => self@.get(key.deep_model()) == Some(*v),
        None => self@.get(key.deep_model()) == None
    })]
    pub fn get(&self, key: &K) -> Option<&V> {
        snapshot! { Tree::<K, V>::has_mapping_model };

        let mut tree = &self.0;
        #[invariant(inv(tree))]
        #[invariant(tree.bst_invariant())]
        #[invariant(forall<v: V> self.0.has_mapping(key.deep_model(), v) == (*tree).has_mapping(key.deep_model(), v))]
        while let Some(node) = &tree.node {
            match key.cmp(&node.key) {
                Less => tree = &node.left,
                Equal => return Some(&node.val),
                Greater => tree = &node.right,
            }
        }
        return None;
    }

    #[ensures(match result {
        Some(v) => self@.get(key.deep_model()) == Some(*v) && (^self)@ == self@.set(key.deep_model(), Some(^v)),
        None => self@.get(key.deep_model()) == None && (^self)@ == self@
    })]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        snapshot! { Tree::<K, V>::has_mapping_model };

        let mut tree = &mut self.0;
        let old_tree = snapshot! { tree };

        #[invariant(inv(tree))]
        #[invariant(tree.bst_invariant())]
        #[invariant(tree.height_invariant())]
        #[invariant(tree.color_invariant())]
        #[invariant(forall<v: V> (^tree).has_mapping(key.deep_model(), v) == (^*old_tree).has_mapping(key.deep_model(), v))]
        #[invariant(forall<v: V> (*tree).has_mapping(key.deep_model(), v) == (**old_tree).has_mapping(key.deep_model(), v))]
        #[invariant((forall<k: K::DeepModelTy, v: V> k == key.deep_model() || (*tree).has_mapping(k, v) == (^tree).has_mapping(k, v))
                    ==> (^tree).bst_invariant() ==> (^*old_tree).bst_invariant())]
        #[invariant((*tree).height() == (^tree).height() && (^tree).height_invariant() ==>
                    (^*old_tree).height_invariant())]
        #[invariant(CPL((*tree).color()).match_t(^tree) ==> CPL(Black).match_t(^*old_tree))]
        #[invariant(forall<k: K::DeepModelTy, v: V> (*tree).has_mapping(k, v) == (^tree).has_mapping(k, v) ==>
                    (**old_tree).has_mapping(k, v) == (^*old_tree).has_mapping(k, v))]
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
