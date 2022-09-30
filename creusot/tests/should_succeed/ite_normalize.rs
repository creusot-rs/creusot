#![feature(allocator_api)]

extern crate creusot_contracts;

use creusot_contracts::{derive::Clone, *};

#[trusted]
struct BTreeMap<K, V>(std::collections::BTreeMap<K, V>);

impl<K: DeepModel, V> BTreeMap<K, V> {
    #[trusted]
    fn new() -> Self {
        Self(std::collections::BTreeMap::new())
    }

    #[trusted]
    #[ensures(result == None ==> (@self).get(key.deep_model()) == None)]
    #[ensures(forall<v: &V> result == Some(v) ==> (@self).get(key.deep_model()) == Some(*v))]
    fn get<'a>(&'a self, key: &'a K) -> Option<&'a V>
    where
        K: Ord,
    {
        self.0.get(key)
    }

    #[trusted]
    #[ensures(forall<i: K::DeepModelTy> (@^self).get(i) == (if i == key.deep_model() { Some(value) } else { (@self).get(i) }))]
    fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        self.0.insert(key, value)
    }
}

impl<K: Clone, V: Clone> Clone for BTreeMap<K, V> {
    #[trusted]
    #[ensures(*self == result)]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K: DeepModel, V> ShallowModel for BTreeMap<K, V> {
    type ShallowModelTy = creusot_contracts::Mapping<K::DeepModelTy, Option<V>>;

    #[logic]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { absurd }
    }
}

#[derive(Clone)]
pub enum Expr {
    IfThenElse { c: Box<Expr>, t: Box<Expr>, e: Box<Expr> },
    Var { v: usize },
    True,
    False,
}

// FIXME: this should go away, we have not defined any order relation on Expr
#[trusted]
impl WellFounded for Expr {}

use std::alloc::Allocator;
extern_spec! {
    mod std {
        mod boxed {
            impl<T : Clone, A : Allocator + Clone> Clone for Box<T, A> {
                #[ensures(result == *self)]
                fn clone(&self) -> Self;
            }
        }
    }
}

impl From<usize> for Expr {
    fn from(a: usize) -> Self {
        Self::variable(a)
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }
}

impl Expr {
    #[ensures(result == Expr::IfThenElse { c: Box::new(c), t: Box::new(t), e: Box::new(e) })]
    pub fn ite(c: Expr, t: Expr, e: Expr) -> Self {
        Self::IfThenElse { c: Box::new(c), t: Box::new(t), e: Box::new(e) }
    }

    pub fn variable(v: usize) -> Self {
        Self::Var { v }
    }

    #[requires(self.is_normalized())]
    #[requires(a.is_normalized())]
    #[requires(b.is_normalized())]
    #[ensures(result.is_normalized())]
    #[variant(self)]
    pub fn transpose(self, a: Self, b: Self) -> Self {
        match self {
            Self::IfThenElse { c, t, e } => Self::IfThenElse {
                c,
                t: Box::new(t.transpose(a.clone(), b.clone())),
                e: Box::new(e.transpose(a, b)),
            },
            Self::Var { .. } => {
                Self::IfThenElse { c: Box::new(self), t: Box::new(a), e: Box::new(b) }
            }
            Self::True => a,
            Self::False => b,
        }
    }

    #[predicate]
    fn is_normalized(self) -> bool {
        match self {
            Expr::IfThenElse { c, t, e } => {
                c.is_normalized()
                    && t.is_normalized()
                    && e.is_normalized()
                    && match *c {
                        Expr::IfThenElse { .. } => false,
                        _ => true,
                    }
            }
            Expr::Var { .. } => true,
            Expr::True => true,
            Expr::False => true,
        }
    }

    #[ensures(result.is_normalized())]
    #[variant(self)]
    pub fn normalize(&self) -> Self {
        match self {
            Expr::IfThenElse { c, t, e } => {
                let cp = c.normalize();
                let tp = t.normalize();
                let ep = e.normalize();
                cp.transpose(tp, ep)
            }
            e => e.clone(),
        }
    }

    #[predicate]
    fn is_simplified(self) -> bool {
        match self {
            Expr::IfThenElse { c, t, e } => match *c {
                Expr::Var { v } => t.does_not_contain(v) && e.does_not_contain(v),
                c => c.is_simplified() && t.is_simplified() && e.is_simplified(),
            },
            _ => true,
        }
    }

    #[predicate]
    fn does_not_contain(self, vp: usize) -> bool {
        match self {
            Expr::IfThenElse { c, t, e } => {
                c.does_not_contain(vp) && t.does_not_contain(vp) && e.does_not_contain(vp)
            }
            Expr::Var { v } => v != vp,
            _ => true,
        }
    }

    #[requires(self.is_normalized())]
    #[ensures(result.is_simplified())]
    pub fn simplify(self) -> Self {
        self.simplify_helper(BTreeMap::new())
    }

    #[requires(self.is_normalized())]
    #[ensures(forall<i: usize> (exists<v: bool> (@state).get(@i) == Some(v)) ==> result.does_not_contain(i))]
    #[ensures(result.is_simplified())]
    #[variant(self)]
    fn simplify_helper(self, state: BTreeMap<usize, bool>) -> Self {
        match self {
            Expr::IfThenElse { c, t, e } => {
                match *c {
                    Expr::Var { v } => {
                        if let Some(b) = state.get(&v) {
                            if *b {
                                t.simplify_helper(state)
                            } else {
                                e.simplify_helper(state)
                            }
                        } else {
                            // Then
                            let mut state_t = state.clone();
                            state_t.insert(v, true);
                            let tp = t.simplify_helper(state_t);

                            // Else
                            let mut state_e = state.clone();
                            state_e.insert(v, false);
                            let ep = e.simplify_helper(state_e);

                            // Composite
                            Self::IfThenElse { c, t: Box::new(tp), e: Box::new(ep) }
                        }
                    }
                    c => c.simplify_helper(state),
                }
            }
            Expr::Var { v } => {
                if let Some(b) = state.get(&v) {
                    if *b {
                        Self::True
                    } else {
                        Self::False
                    }
                } else {
                    Expr::Var { v }
                }
            }
            c => c,
        }
    }
}
