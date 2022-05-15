#![feature(box_patterns)]
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;
use std::cmp::Ord;
use std::cmp::Ordering::*;
use std::mem::{swap, replace};

extern_spec! {
    #[ensures(result == (@self_).cmp_log(@*o))]
    fn std::cmp::Ord::cmp<Self_>(self_: &Self_, o: &Self_) -> Ordering
        where Self_: Ord + Model,
              Self_::ModelTy: OrdLogic
}

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

impl<K: Model, V> Tree<K, V> {
    #[predicate]
    fn has_mapping(self, k: K::ModelTy, v: V) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => false,
                Tree { node: Some(box Node { left, color, key, val, right }) } =>
                    left.has_mapping(k, v) || right.has_mapping(k, v) || k == @key && v == val
            }
        }
    }

    #[predicate]
    fn same_mappings(self, o: Self) -> bool {
        pearlite! {
            forall<k: K::ModelTy, v: V> self.has_mapping(k, v) == o.has_mapping(k, v)
        }
    }

    #[logic]
    fn model_acc(self, accu: <Self as Model>::ModelTy) -> <Self as Model>::ModelTy {
        pearlite! {
            match self {
                Tree { node: None } => accu,
                Tree { node: Some(box Node { left, color, key, val, right }) } => {
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(@key, Some(val));
                    right.model_acc(accu2)
                }
            }
        }
    }

    #[logic]
    #[ensures(self.model_acc(accu).get(k) == accu.get(k) ||
              exists<v: V> self.model_acc(accu).get(k) == Some(v) && self.has_mapping(k, v))]
    fn model_acc_has_binding(self, accu: <Self as Model>::ModelTy, k: K::ModelTy) {
        pearlite! {
            match self {
                Tree { node: None } => (),
                Tree { node: Some(box Node { left, color, key, val, right }) } => {
                    left.model_acc_has_binding(accu, k);
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(@key, Some(val));
                    right.model_acc_has_binding(accu2, k)
                }
            }
        }
    }

    #[logic]
    #[requires(self.bst_invariant())]
    #[ensures(forall<v: V> self.has_mapping(k, v) ==> self.model_acc(accu).get(k) == Some(v))]
    fn has_binding_model_acc(self, accu: <Self as Model>::ModelTy, k: K::ModelTy)
    where
        K::ModelTy: OrdLogic,
    {
        pearlite! {
            match self {
                Tree { node: None } => (),
                Tree { node: Some(box Node { left, color, key, val, right }) } => {
                    left.has_binding_model_acc(accu, k);
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(@key, Some(val));
                    right.has_binding_model_acc(accu2, k);
                    right.model_acc_has_binding(accu2, k)
                }
            }
        }
    }

    #[logic]
    #[requires(self.bst_invariant())]
    #[ensures(self.has_mapping(k, v) == ((@self).get(k) == Some(v)))]
    fn has_binding_model(self, k: K::ModelTy, v: V)
    where
        K::ModelTy: OrdLogic,
    {
        pearlite! { {
            self.model_acc_has_binding(Mapping::cst(None), k);
            self.has_binding_model_acc(Mapping::cst(None), k)
        } }
    }
}

impl<K: Model, V> Node<K, V> {
    #[predicate]
    fn same_mappings(self, o: Self) -> bool {
        pearlite! {
            forall<st: Tree<K, V>, ot: Tree<K, V>>
                (match st { Tree { node: Some(x) } => self == *x, _ => false }) &&
                (match ot { Tree { node: Some(x) } => o == *x, _ => false }) ==>
                st.same_mappings(ot)
        }
    }
}

impl<K: Model, V> Model for Node<K, V> {
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

/*******************************  The BST invariant ***************************/

impl<K: Model, V> Node<K, V>
where
    K::ModelTy: OrdLogic,
{
    #[predicate]
    fn bst_invariant_here(self) -> bool {
        pearlite! {
            (forall<k: K::ModelTy, v: V> self.left.has_mapping(k, v) ==> k < @self.key) &&
            (forall<k: K::ModelTy, v: V> self.right.has_mapping(k, v) ==> @self.key < k)
        }
    }

    #[predicate]
    fn bst_invariant(self) -> bool {
        pearlite! {
            self.bst_invariant_here() && self.left.bst_invariant() && self.right.bst_invariant()
        }
    }
}

impl<K: Model, V> Tree<K, V>
where
    K::ModelTy: OrdLogic,
{
    #[predicate]
    fn bst_invariant(self) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => true,
                Tree { node: Some(box node) } => {
                    let Node { left, color, key, val, right } = node;
                    node.bst_invariant_here() && left.bst_invariant() && right.bst_invariant()
                }
            }
        }
    }
}

/******************************  The color invariant **************************/

impl<K, V> Tree<K, V> {
    #[predicate]
    fn is_red_log(self) -> bool {
        match self.node {
            Some(box Node { left, color: Red, key, val, right }) => true,
            _ => false,
        }
    }

    #[predicate]
    fn color_invariant(self) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => true,
                Tree { node: Some(box node) } => {
                    let Node { left, color, key, val, right } = node;
                    node.color_invariant_here() && left.color_invariant() && right.color_invariant()
                }
            }
        }
    }
}

impl<K, V> Node<K, V> {
    #[predicate]
    fn color_invariant_here(self) -> bool {
        pearlite! { !self.right.is_red_log() && (self.color == Red ==> !self.left.is_red_log()) }
    }

    #[predicate]
    fn color_invariant(self) -> bool {
        self.color_invariant_here() && self.left.color_invariant() && self.right.color_invariant()
    }
}

/*****************************  The height invariant  *************************/

impl<K, V> Node<K, V> {
    #[predicate]
    fn has_height(self, h: Int) -> bool {
        match self {
            Node { left, color: Red, key, val, right } => left.has_height(h) && right.has_height(h),
            Node { left, color: Black, key, val, right } => {
                left.has_height(h - 1) && right.has_height(h - 1)
            }
        }
    }
}

impl<K, V> Tree<K, V> {
    #[predicate]
    fn has_height(self, h: Int) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => h == 0,
                Tree { node: Some(box Node { left, color: Red, key, val, right }) } =>
                    left.has_height(h) && right.has_height(h),
                Tree { node: Some(box Node { left, color: Black, key, val, right }) } =>
                    left.has_height(h-1) && right.has_height(h-1)
            }
        }
    }
}

/*************************  Conjunction of invariants  ************************/

impl<K: Model, V> Tree<K, V>
where
    K::ModelTy: OrdLogic,
{
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            self.bst_invariant() && self.color_invariant() &&
            exists<h: Int> self.has_height(h)
        }
    }
}

/*************************  Code of the data structure  ***********************/

impl<K: Model, V> Tree<K, V> {
    #[ensures(result == self.is_red_log())]
    fn is_red(&self) -> bool {
        match self.node {
            Some(box Node { color: Red, .. }) => true,
            _ => false,
        }
    }
}

impl<K: Model, V> Node<K, V>
where
    K::ModelTy: OrdLogic,
{
    #[requires((*self).bst_invariant())]
    #[requires((*self).left.is_red_log())]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).bst_invariant())]
    #[ensures((^self).right.is_red_log())]
    #[ensures((^self).color == (*self).color)]
    #[ensures(exists<l: Box<Self>, r: Box<Self>>
              (*self).left.node == Some(l) && (^self).right.node == Some(r) &&
              ((^self).left, r.left, r.right) == (l.left, l.right, (*self).right))]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    fn rotate_right(&mut self) {
        let old_self = Ghost::record(&*self);

        //     self
        //    /    \
        //   x      c
        //  / \
        // a   b
        // Rip out the left subtree
        let mut x: Box<_> = match replace(&mut self.left.node, None) {
            Some(x) => x,
            None => panic!(),
        };

        //     self
        //         \
        //   x      c
        //  / \
        // a   b
        swap(&mut self.left, &mut x.right);
        //        self
        //       /    \
        //   x  b      c
        //  /
        // a
        swap(self, &mut x);
        self.color = x.color;
        x.color = Red;
        //   self
        //  /
        // a      x
        //       / \
        //      b   c
        proof_assert! { (@old_self).left.has_mapping(@(*self).key, (*self).val) }
        proof_assert! { forall<k: K::ModelTy, v: V> x.left.has_mapping(k, v) ==> (@old_self).left.has_mapping(k, v) }
        self.right = Tree { node: Some(x) };
        //   self
        //  /    \
        // a      x
        //       / \
        //      b   c
    }

    #[requires((*self).bst_invariant())]
    #[requires((*self).right.is_red_log())]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).bst_invariant())]
    #[ensures((^self).left.is_red_log())]
    #[ensures((^self).color == (*self).color)]
    #[ensures(exists<l: Box<Self>, r: Box<Self>>
              (*self).right.node == Some(r) && (^self).left.node == Some(l) &&
              (l.left, l.right, (^self).right) == ((*self).left, r.left, r.right))]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    fn rotate_left(&mut self) {
        let old_self = Ghost::record(&*self);

        let mut x: Box<_> = match replace(&mut self.right.node, None) {
            Some(x) => x,
            None => panic!(),
        };
        swap(&mut self.right, &mut x.left);
        swap(self, &mut x);
        self.color = x.color;
        x.color = Red;
        proof_assert! { (@old_self).right.has_mapping(@(*self).key, (*self).val) }
        proof_assert! { forall<k: K::ModelTy, v: V> x.right.has_mapping(k, v) ==> (@old_self).right.has_mapping(k, v) }
        self.left = Tree { node: Some(x) };
    }

    #[requires((*self).bst_invariant())]
    #[requires(!((*self).left.node == None))]
    #[requires(!((*self).right.node == None))]
    #[requires((*self).left.is_red_log() == (*self).right.is_red_log())]
    #[requires(!((*self).color == Red) == (*self).right.is_red_log())]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    #[ensures((^self).bst_invariant())]
    #[ensures((*self).same_mappings(^self))]
    #[ensures(exists<l1: Box<Self>, l2: Box<Self>> (*self).left.node == Some(l1) && (^self).left.node == Some(l2) &&
              l1.left == l2.left && l1.right == l2.right &&
              (*self).color == l2.color && (^self).color == l1.color)]
    #[ensures(exists<r1: Box<Self>, r2: Box<Self>> (*self).right.node == Some(r1) && (^self).right.node == Some(r2) &&
              r1.left == r2.left && r1.right == r2.right &&
              (*self).color == r2.color && (^self).color == r1.color)]
    fn flip_colors(&mut self) {
        self.left.node.as_mut().unwrap().color = self.color;
        swap(&mut self.color, &mut self.right.node.as_mut().unwrap().color);
        proof_assert!((*self).left.same_mappings((^self).left));
        proof_assert!((*self).right.same_mappings((^self).right));
    }

    #[requires((*self).bst_invariant())]
    #[requires((*self).color == Red && (*self).left.is_red_log() ==>
               (*self).left.color_invariant())]
    #[requires((*self).color == Red && (*self).right.is_red_log() ==>
               (*self).right.color_invariant())]
    #[requires((*self).color == Red && (*self).right.is_red_log() && (*self).left.is_red_log() ==> false)]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).bst_invariant())]
    #[ensures((*self).left.color_invariant() && !(*self).right.is_red_log() ==>
              (*self) == (^self))]
    #[ensures(forall<l: Box<Self>> (*self).left.node == Some(l) &&
              (*self).color == Black && l.color == Red &&
              l.left.is_red_log() && l.left.color_invariant() &&
              !l.right.is_red_log() && l.right.color_invariant() &&
              !(*self).right.is_red_log() && (*self).right.color_invariant() ==>
              (^self).color == Red && (^self).color_invariant())]
    #[ensures(!(*self).left.is_red_log() && (*self).left.color_invariant() &&
              (*self).right.is_red_log() && (*self).right.color_invariant() ==>
              (^self).left.is_red_log() && (^self).left.color_invariant() &&
              !(^self).right.is_red_log() && (^self).right.color_invariant() &&
              (^self).color == (*self).color)]
    #[ensures((*self).color == Black &&
              (*self).left.is_red_log() && (*self).left.color_invariant() &&
              (*self).right.is_red_log() && (*self).right.color_invariant() ==>
              (^self).color == Red && (^self).color_invariant())]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
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
}

impl<K: Model + Ord, V> Tree<K, V>
where
    K::ModelTy: OrdLogic
{
    #[ensures(@result == Mapping::cst(None))]
    #[ensures(result.invariant())]
    pub fn new() -> Tree<K, V> {
        Tree { node: None }
    }

    #[requires((*self).bst_invariant())]
    #[requires((*self).color_invariant())]
    #[ensures((^self).bst_invariant())]
    #[ensures(exists<node: Box<Node<K, V>>> (^self).node == Some(node) &&
              !node.right.is_red_log() &&
              node.left.color_invariant() && node.right.color_invariant())]
    #[ensures(!(*self).is_red_log() ==> (^self).color_invariant())]
    #[ensures((^self).has_mapping(@key, val))]
    #[ensures(forall<k: K::ModelTy, v: V> k == @key || (*self).has_mapping(k, v) == (^self).has_mapping(k, v))]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    fn insert_rec(&mut self, key: K, val: V) {
        let old_self = Ghost::record(&*self);
        match &mut self.node {
            None => {
                self.node = Some(Box::new(Node {
                    left: Tree { node: None },
                    color: Red,
                    key,
                    val,
                    right: Tree { node: None },
                }));
                return;
            }
            Some(node) => {
                match key.cmp(&node.key) {
                    Less => node.left.insert_rec(key, val),
                    Equal => {
                        node.val = val;
                        return;
                    }
                    Greater => node.right.insert_rec(key, val),
                }
                proof_assert!(forall<h: Int> (@old_self).has_height(h) ==> node.has_height(h));

                node.balance();
            }
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(@^self == (@*self).set(@key, Some(val)))]
    pub fn insert(&mut self, key: K, val: V) {
        let old_self = Ghost::record(&*self);
        self.insert_rec(key, val);
        self.node.as_mut().unwrap().color = Black;
        proof_assert! { forall<h: Int> (@old_self).has_height(h) ==>
        (*self).has_height(h) || (*self).has_height(h+1) }
        proof_assert! { (*self).has_binding_model(@key /* dummy */, val /* dummy */); true }
    }

    #[requires((*self).bst_invariant())]
    #[ensures(forall<r: &V> result == Some(r) ==> (*self).has_mapping(@*key, *r))]
    #[ensures(result == None ==> forall<v: V> !(*self).has_mapping(@*key, v))]
    fn get_rec(&self, key: &K) -> Option<&V> {
        match &self.node {
            None => None,
            Some(node) => match key.cmp(&node.key) {
                Less => node.left.get_rec(key),
                Equal => Some(&node.val),
                Greater => node.right.get_rec(key),
            },
        }
    }

    #[requires((*self).invariant())]
    #[ensures(forall<v: &V> (result == Some(v)) == ((@*self).get(@*key) == Some(*v)))]
    #[ensures((result == None) == ((@*self).get(@*key) == None))]
    pub fn get(&self, key: &K) -> Option<&V> {
        proof_assert! { forall<v:V> { self.has_binding_model(@*key, v); true } }
        self.get_rec(key)
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).is_red_log() == (*self).is_red_log())]
    #[ensures(forall<r: &mut V> result == Some(r) ==> (*self).has_mapping(@*key, *r) && (^self).has_mapping(@*key, ^r))]
    #[ensures(result == None ==> forall<v: V> !(*self).has_mapping(@*key, v) && !(^self).has_mapping(@*key, v))]
    #[ensures(forall<k: K::ModelTy, v: V> k == @key || (*self).has_mapping(k, v) == (^self).has_mapping(k, v))]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    fn get_mut_rec(&mut self, key: &K) -> Option<&mut V> {
        match &mut self.node {
            None => None,
            Some(node) => match key.cmp(&node.key) {
                Less => node.left.get_mut_rec(key),
                Equal => Some(&mut node.val),
                Greater => node.right.get_mut_rec(key),
            },
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(forall<v: &mut V> result == Some(v) ==>
              (@*self).get(@*key) == Some(*v) && @^self == (@*self).set(@key, Some(^v)))]
    #[ensures(result == None ==> (@*self).get(@*key) == None && (@^self).get(@*key) == None)]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        proof_assert! { forall<v:V> { self.has_binding_model(@*key, v); true } }
        self.get_mut_rec(key)
    }
}
