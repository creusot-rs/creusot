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
    fn model_acc_has_mapping(self, accu: <Self as Model>::ModelTy, k: K::ModelTy) {
        pearlite! {
            match self {
                Tree { node: None } => (),
                Tree { node: Some(box Node { left, color, key, val, right }) } => {
                    left.model_acc_has_mapping(accu, k);
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(@key, Some(val));
                    right.model_acc_has_mapping(accu2, k)
                }
            }
        }
    }

    #[logic]
    #[requires(self.bst_invariant())]
    #[ensures(forall<v: V> self.has_mapping(k, v) ==> self.model_acc(accu).get(k) == Some(v))]
    fn has_mapping_model_acc(self, accu: <Self as Model>::ModelTy, k: K::ModelTy)
    where
        K::ModelTy: OrdLogic,
    {
        pearlite! {
            match self {
                Tree { node: None } => (),
                Tree { node: Some(box Node { left, color, key, val, right }) } => {
                    left.has_mapping_model_acc(accu, k);
                    let accu1 = left.model_acc(accu);
                    let accu2 = accu1.set(@key, Some(val));
                    right.has_mapping_model_acc(accu2, k);
                    right.model_acc_has_mapping(accu2, k)
                }
            }
        }
    }

    #[logic]
    #[requires(self.bst_invariant())]
    #[ensures(self.has_mapping(k, v) == ((@self).get(k) == Some(v)))]
    fn has_mapping_model(self, k: K::ModelTy, v: V)
    where
        K::ModelTy: OrdLogic,
    {
        pearlite! { {
            self.model_acc_has_mapping(Mapping::cst(None), k);
            self.has_mapping_model_acc(Mapping::cst(None), k)
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
    #[logic]
    fn color(self) -> Color {
        match self.node {
            Some(box Node { left, color, key, val, right }) => color,
            _ => Black,
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
        pearlite! { self.right.color() == Black && (self.color == Red ==> self.left.color() == Black) }
    }

    #[predicate]
    fn color_invariant(self) -> bool {
        self.color_invariant_here() && self.left.color_invariant() && self.right.color_invariant()
    }
}

/*****************************  The height invariant  *************************/

impl<K, V> Node<K, V> {
    #[predicate]
    #[ensures(forall<tree: Tree<K, V>, node: Box<Node<K, V>>>
              tree.node == Some(node) && self == *node ==>
              result == tree.has_height_rec(h))]
    fn has_height(self, h: Int) -> bool {
        pearlite! {
            match self {
                Node { left, color: Red, key, val, right } =>
                    left.has_height_rec(h) && right.has_height_rec(h),
                Node { left, color: Black, key, val, right } => {
                    left.has_height_rec(h - 1) && right.has_height_rec(h - 1)
                }
            }
        }
    }
}

impl<K, V> Tree<K, V> {
    #[predicate]
    #[ensures(result ==> h >= 0)]
    fn has_height_rec(self, h: Int) -> bool {
        pearlite! {
            match self {
                Tree { node: None } => h == 0,
                Tree { node: Some(box Node { left, color: Red, key, val, right }) } =>
                    left.has_height_rec(h) && right.has_height_rec(h),
                Tree { node: Some(box Node { left, color: Black, key, val, right }) } =>
                    left.has_height_rec(h - 1) && right.has_height_rec(h - 1)
            }
        }
    }

    #[predicate]
    #[ensures(self.node == None ==> result == (h == 0))]
    #[ensures(forall<node: Box<Node<K, V>>> self.node == Some(node) ==> result == node.has_height(h))]
    fn has_height(self, h: Int) -> bool {
        self.has_height_rec(h)
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
            self.bst_invariant() && self.color_invariant() && self.color() == Black &&
            exists<h: Int> self.has_height(h)
        }
    }
}

/*************************  Code of the data structure  ***********************/

impl<K: Model, V> Tree<K, V> {
    #[ensures(result == (self.color() == Red))]
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
    #[requires((*self).left.color() == Red)]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).bst_invariant())]
    #[ensures((^self).right.color() == Red)]
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
    #[requires((*self).right.color() == Red)]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).bst_invariant())]
    #[ensures((^self).left.color() == Red)]
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
    #[requires((*self).left.node != None)]
    #[requires((*self).right.node != None)]
    #[requires((*self).left.color() == (*self).right.color())]
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
        proof_assert!((*self).bst_invariant_here());
    }

    #[requires((*self).bst_invariant())]
    #[requires((*self).color == Red && (*self).left.color() == Red ==>
               (*self).left.color_invariant())]
    #[requires((*self).color == Red && (*self).right.color() == Red ==>
               (*self).right.color_invariant())]
    #[requires((*self).color == Red && (*self).right.color() == Red && (*self).left.color() == Red ==> false)]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).bst_invariant())]
    #[ensures((*self).left.color_invariant() && (*self).right.color() == Black ==>
              (*self) == (^self))]
    #[ensures(forall<l: Box<Self>> (*self).left.node == Some(l) &&
              (*self).color == Black && l.color == Red &&
              l.left.color() == Red && l.left.color_invariant() &&
              l.right.color() == Black && l.right.color_invariant() &&
              (*self).right.color() == Black && (*self).right.color_invariant() ==>
              (^self).color == Red && (^self).color_invariant())]
    #[ensures((*self).left.color() == Black && (*self).left.color_invariant() &&
              (*self).right.color() == Red && (*self).right.color_invariant() ==>
              (^self).left.color() == Red && (^self).left.color_invariant() &&
              (^self).right.color() == Black && (^self).right.color_invariant() &&
              (^self).color == (*self).color)]
    #[ensures((*self).color == Black &&
              (*self).left.color() == Red && (*self).left.color_invariant() &&
              (*self).right.color() == Red && (*self).right.color_invariant() ==>
              (^self).color == Red && (^self).color_invariant())]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    fn balance(&mut self) {
        if self.right.is_red() && !self.left.is_red() {
            // B(B, R)
            self.rotate_left();
            // B(R, B)
        }

        if self.left.is_red() && self.left.node.as_ref().unwrap().left.is_red() {
            self.rotate_right();
        }

        if self.left.is_red() && self.right.is_red() {
            self.flip_colors();
        }
    }

    #[requires((*self).bst_invariant())]
    #[requires((*self).color_invariant())]
    #[requires((*self).color == Red)]
    #[requires(exists<l: Box<Self>> (*self).left.node == Some(l) && l.color == Black && l.left.color() == Black)]
    #[requires(exists<r: Box<Self>> (*self).right.node == Some(r) && r.color == Black)]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    #[ensures((^self).bst_invariant())]
    #[ensures((*self).same_mappings(^self))]
    #[ensures((^self).color == Red ==>
              (^self).color_invariant() &&
              exists<l: Box<Self>> (^self).left.node == Some(l) && l.left.color() == Red)]
    #[ensures((^self).color == Black ==>
              (^self).left.color() == Red && (^self).left.color_invariant() &&
              (^self).right.color() == Red && (^self).right.color_invariant())]
    fn move_red_left(&mut self) {
        let old_self = Ghost::record(&*self);
        self.flip_colors();
        if self.right.node.as_mut().unwrap().left.is_red() {
            self.right.node.as_mut().unwrap().rotate_right();
            proof_assert!((@old_self).same_mappings(*self));
            self.rotate_left();
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
    #[ensures(exists<node: Box<Node<K, V>>> (^self).node == Some(node) && node.right.color() == Black &&
              node.left.color_invariant() && node.right.color_invariant())]
    #[ensures((*self).color() == Black ==> (^self).color_invariant())]
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
        proof_assert! { (*self).has_mapping_model(@key /* dummy */, val /* dummy */); true }
    }

    #[requires((*self).bst_invariant())]
    #[requires((*self).color_invariant())]
    #[requires(exists<node: Box<Node<K, V>>> (*self).node == Some(node) &&
               (node.color == Red || node.left.color() == Red))]
    #[requires(exists<h: Int> (*self).has_height(h))]
    #[ensures((^self).bst_invariant())]
    #[ensures((*self).has_mapping(@result.0, result.1))]
    #[ensures(forall<k: K::ModelTy, v: V> (*self).has_mapping(k, v) ==> @result.0 <= k)]
    #[ensures(forall<k: K::ModelTy, v: V> (*self).has_mapping(k, v) ==>
              @result.0 == k || (^self).has_mapping(k, v))]
    #[ensures(forall<k: K::ModelTy, v: V> (^self).has_mapping(k, v) ==>
              @result.0 != k && (*self).has_mapping(k, v))]
    #[ensures(forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h))]
    #[ensures((^self).color_invariant())]
    #[ensures((*self).color() == Black ==> (^self).color() == Black)]
    fn delete_min_rec(&mut self) -> (K, V) {
        let old_self = Ghost::record(&*self);
        let node = self.node.as_mut().unwrap();
        if let None = node.left.node {
            let node = replace(&mut self.node, None).unwrap();
            return (node.key, node.val)
        }
        if !node.left.is_red() && !node.left.node.as_ref().unwrap().left.is_red() {
            node.move_red_left();
        }
        proof_assert!(forall<h: Int> (@old_self).has_height(h) ==> (*node).has_height(h));
        let r = node.left.delete_min_rec();
        proof_assert!(forall<h: Int> (@old_self).has_height(h) ==> (*node).has_height(h));
        node.balance();
        r
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(result == None ==> @^self == @*self && @*self == Mapping::cst(None))]
    #[ensures(forall<k: K, v: V> result == Some((k, v)) ==>
              (@*self).get(@k) == Some(v) &&
              (forall<k2: K::ModelTy> (@*self).get(k2) == None || @k <= k2) &&
              @^self == (@*self).set(@k, None))]
    pub fn delete_min(&mut self) -> Option<(K, V)> {
        let old_self = Ghost::record(&*self);
        match &mut self.node {
            None => return None,
            Some(node) =>
                if !node.left.is_red() && !node.right.is_red() {
                    node.color = Red;
                }
        }
        proof_assert! { forall<h: Int> (@old_self).has_height(h) ==>
                        (*self).color() == Black || (*self).has_height(h-1) }
        let r = self.delete_min_rec();
        if self.is_red() { self.node.as_mut().unwrap().color = Black; }
        proof_assert! { forall<h: Int> (@old_self).has_height(h) ==>
                        (*self).has_height(h) || (*self).has_height(h-1) }
        proof_assert! { (*self).has_mapping_model(@r.0 /* dummy */, r.1 /* dummy */); true }
        Some(r)
    }

    #[requires((*self).invariant())]
    #[ensures(forall<v: &V> result == Some(v) ==> (@*self).get(@*key) == Some(*v))]
    #[ensures(result == None ==> (@*self).get(@*key) == None)]
    pub fn get(&self, key: &K) -> Option<&V> {
        proof_assert! { forall<v:V> { self.has_mapping_model(@*key, v); true } }

        let mut tree = self;
        #[invariant(bst_inv, (*tree).bst_invariant())]
        #[invariant(has_mapping, forall<v: V> (*self).has_mapping(@*key, v) == (*tree).has_mapping(@*key, v))]
        while let Some(node) = &tree.node {
            match key.cmp(&node.key) {
                Less => tree = &node.left,
                Equal => return Some(&node.val),
                Greater => tree = &node.right
            }
        }
        return None
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(forall<v: &mut V> result == Some(v) ==>
              (@*self).get(@*key) == Some(*v) && @^self == (@*self).set(@key, Some(^v)))]
    #[ensures(result == None ==> (@*self).get(@*key) == None && (@^self).get(@*key) == None)]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        proof_assert! { forall<v:V> { self.has_mapping_model(@*key, v); true } }

        let mut tree = self;

        #[invariant(bst_inv, (*tree).bst_invariant())]
        #[invariant(color_inv, (*tree).color_invariant())]
        #[invariant(mapping_prof_key, forall<v: V> (^tree).has_mapping(@key, v) == (^self).has_mapping(@key, v))]
        #[invariant(mapping_cur_key, forall<v: V> (*tree).has_mapping(@key, v) == (*self).has_mapping(@key, v))]
        #[invariant(bst_inv_proph, (forall<k: K::ModelTy, v: V> k == @key || (*tree).has_mapping(k, v) == (^tree).has_mapping(k, v))
                    ==> (^tree).bst_invariant() ==> (^self).bst_invariant())]
        #[invariant(color_inv_proph, (^tree).color_invariant() && (^tree).color() == (*tree).color() ==> (^self).color_invariant())]
        #[invariant(color_proph, (^tree).color() == (*tree).color() ==> (^self).color() == (*self).color())]
        #[invariant(mapping_proph, forall<k: K::ModelTy, v: V> (*tree).has_mapping(k, v) == (^tree).has_mapping(k, v) ==>
                    (*self).has_mapping(k, v) == (^self).has_mapping(k, v))]
        #[invariant(height, (^tree).color() == (*tree).color() &&
                    (forall<h: Int> (*tree).has_height(h) ==> (^tree).has_height(h)) ==>
                    (forall<h: Int> (*self).has_height(h) ==> (^self).has_height(h)))]
        while let Some(node) = &mut tree.node {
            match key.cmp(&node.key) {
                Less => tree = &mut node.left,
                Equal => return Some(&mut node.val),
                Greater => tree = &mut node.right
            }
        }
        return None
    }
}
