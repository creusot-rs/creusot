// UNSTABLE
extern crate creusot_contracts;

use creusot_contracts::{invariant::Invariant, logic::Mapping, Clone, PartialEq, *};
use std::cmp::Ordering::*;

/* Axiomatization of bumpalo */

mod bumpalo {
    use creusot_contracts::*;

    #[trusted]
    pub struct Bump();

    impl Bump {
        #[trusted]
        #[ensures(*result == val)]
        pub fn alloc<T>(&self, val: T) -> &mut T {
            panic!()
        }
    }
}

/* Axiomatization of a HashMap library */

mod hashmap {
    use creusot_contracts::{logic::Mapping, *};

    pub trait Hash: DeepModel {
        #[ensures(result@ == Self::hash_log(self.deep_model()))]
        fn hash(&self) -> u64;

        #[ghost]
        fn hash_log(_: Self::DeepModelTy) -> Int;
    }

    #[trusted]
    pub struct MyHashMap<K, V>(std::marker::PhantomData<(K, V)>);

    impl<K: Hash, V> ShallowModel for MyHashMap<K, V> {
        type ShallowModelTy = Mapping<K::DeepModelTy, Option<V>>;

        #[ghost]
        #[open(self)]
        #[trusted]
        fn shallow_model(self) -> Self::ShallowModelTy {
            absurd
        }
    }

    impl<K: Hash + Eq + DeepModel, V> MyHashMap<K, V> {
        #[ensures(forall<i: K::DeepModelTy> (^self)@.get(i) == (if i == key.deep_model() { Some(val) } else { self@.get(i) } ))]
        #[trusted]
        pub fn add(&mut self, key: K, val: V) {
            panic!()
        }

        #[ensures(match result {
            Some(v) => self@.get(key.deep_model()) == Some(*v),
            None => self@.get(key.deep_model()) == None,
        })]
        #[trusted]
        pub fn get<'a, 'b>(&'a self, key: &'b K) -> Option<&'a V> {
            panic!()
        }

        #[ensures(result@ == Mapping::cst(None))]
        #[trusted]
        pub fn new() -> Self {
            panic!()
        }
    }

    impl<U: Hash, V: Hash> Hash for (U, V) {
        #[ensures(result@ == Self::hash_log(self.deep_model()))]
        fn hash(&self) -> u64 {
            self.0.hash().wrapping_add(self.1.hash().wrapping_mul(17))
        }

        #[open(self)]
        #[ghost]
        fn hash_log(x: Self::DeepModelTy) -> Int {
            pearlite! { (U::hash_log(x.0) + V::hash_log(x.1) * 17) % (u64::MAX@ + 1) }
        }
    }
}

/* The Bdd library */

#[derive(Eq, PartialEq, Clone, Copy)]
enum Node<'arena> {
    False,
    True,
    If { v: u64, childt: Bdd<'arena>, childf: Bdd<'arena> },
}
use self::Node::*;

enum NodeLog {
    False,
    True,
    If { v: u64, childt: u64, childf: u64 },
}

#[derive(Copy, Eq)]
pub struct Bdd<'arena>(&'arena Node<'arena>, u64);

impl<'arena> Clone for Bdd<'arena> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'arena> hashmap::Hash for Node<'arena> {
    #[ensures(result@ == Self::hash_log(self@))]
    fn hash(&self) -> u64 {
        match self {
            False => 1,
            True => 2,
            If { v, childt, childf } => {
                v.wrapping_add(childt.1.wrapping_mul(5)).wrapping_add(childf.1.wrapping_mul(7))
            }
        }
    }

    #[open(self)]
    #[ghost]
    fn hash_log(x: Self::DeepModelTy) -> Int {
        pearlite! {
            match x {
                NodeLog::False => 1,
                NodeLog::True => 2,
                NodeLog::If { v, childt, childf } =>
                    (v@ + childt@ * 5 + childf@ * 7) % (u64::MAX@ + 1)
            }
        }
    }
}

impl<'arena> hashmap::Hash for Bdd<'arena> {
    #[ensures(result@ == Self::hash_log(self@))]
    fn hash(&self) -> u64 {
        self.1
    }

    #[open(self)]
    #[ghost]
    fn hash_log(x: Self::DeepModelTy) -> Int {
        pearlite! { x@ }
    }
}

impl<'arena> DeepModel for Node<'arena> {
    type DeepModelTy = NodeLog;

    #[open(self)]
    #[ghost]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! {
            match self {
                False => NodeLog::False,
                True => NodeLog::True,
                If { v, childt, childf } => NodeLog::If { v, childt:childt.1, childf:childf.1 }
            }

        }
    }
}

impl<'arena> ShallowModel for Node<'arena> {
    type ShallowModelTy = NodeLog;

    #[open(self)]
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.deep_model() }
    }
}

impl<'arena> DeepModel for Bdd<'arena> {
    type DeepModelTy = u64;

    #[open(self)]
    #[ghost]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self.1 }
    }
}

impl<'arena> ShallowModel for Bdd<'arena> {
    type ShallowModelTy = u64;

    #[open(self)]
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.deep_model() }
    }
}

impl<'arena> PartialEq for Bdd<'arena> {
    #[ensures(result == (self@ == o@))]
    fn eq(&self, o: &Self) -> bool {
        self.1 == o.1
    }
}

impl<'arena> Bdd<'arena> {
    #[ghost]
    fn interp(self, vars: Mapping<u64, bool>) -> bool {
        pearlite! {
            match self {
                Bdd(True, _) => true,
                Bdd(False, _) => false,
                Bdd(If{ v, childt, childf }, _) => {
                    if vars.get(*v) { childt.interp(vars) }
                    else { childf.interp(vars) }
                }
            }
        }
    }

    #[ghost]
    #[ensures(result >= 0)]
    fn size(self) -> Int {
        pearlite! {
            match self {
                Bdd(True, _) => 0,
                Bdd(False, _) => 0,
                Bdd(If{ childt, childf, .. }, _) => {
                    let ht = childt.size();
                    let hf = childf.size();
                    1 + ht + hf
                }
            }
        }
    }

    #[ghost]
    fn leastvar(self) -> Int {
        pearlite! {
            match self {
                Bdd(True, _) => u64::MAX@+1,
                Bdd(False, _) => u64::MAX@+1,
                Bdd(If{ v, .. }, _) => v@
            }
        }
    }
}

pub struct Context<'arena> {
    alloc: &'arena bumpalo::Bump,
    hashcons: hashmap::MyHashMap<Node<'arena>, Bdd<'arena>>,
    hashcons_ghost: Ghost<Mapping<u64, &'arena Node<'arena>>>,
    not_memo: hashmap::MyHashMap<Bdd<'arena>, Bdd<'arena>>,
    and_memo: hashmap::MyHashMap<(Bdd<'arena>, Bdd<'arena>), Bdd<'arena>>,
    cnt: u64,
}

impl<'arena> Invariant for Context<'arena> {
    #[open(self)]
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<n: NodeLog>
                match self.hashcons@.get(n) {
                    Some(b) => b.0@ == n && self.is_valid_node(*b.0) && b.1 < self.cnt &&
                              self.hashcons_ghost.get(b.1) == b.0,
                    None => true
                }) &&
            (forall<bm: u64>
                match self.not_memo@.get(bm) {
                    None => true,
                    Some(n) => {
                        let b = Bdd (self.hashcons_ghost.get(bm), bm);
                        self.is_valid_bdd(n) && self.is_valid_bdd(b) &&
                        (forall<v:_> n.interp(v) == !b.interp(v)) &&
                        b.leastvar() <= n.leastvar()
                }}) &&
            (forall<abm: (u64, u64)>
                match self.and_memo@.get(abm) {
                    None => true,
                    Some(n) => {
                        let a = Bdd (self.hashcons_ghost.get(abm.0), abm.0);
                        let b = Bdd (self.hashcons_ghost.get(abm.1), abm.1);
                        self.is_valid_bdd(n) && self.is_valid_bdd(a) && self.is_valid_bdd(b) &&
                        (forall<v:_> n.interp(v) == (a.interp(v) && b.interp(v))) &&
                        (a.leastvar() <= n.leastvar() || b.leastvar() <= n.leastvar())
                }})
        }
    }
}

impl<'arena> Context<'arena> {
    #[open(self)]
    #[predicate]
    pub fn grows(&mut self) -> bool {
        pearlite! {
            self.cnt@ <= (^self).cnt@ &&
            forall<n: NodeLog>
                match self.hashcons@.get(n) {
                    Some(b) => (^self).hashcons@.get(n) == Some(b),
                    None => true
                }
        }
    }

    #[open(self)]
    #[predicate]
    pub fn is_valid_bdd(self, b: Bdd<'arena>) -> bool {
        pearlite! {
            self.hashcons@.get(b.0@) == Some(b)
        }
    }

    #[predicate]
    fn is_valid_node(self, n: Node<'arena>) -> bool {
        pearlite! {
            match n {
                True => true,
                False => true,
                If{v, childt, childf} =>
                    childt.0 != childf.0 &&
                    self.is_valid_bdd(childt) &&
                    self.is_valid_bdd(childf) &&
                    v@ < childt.leastvar() &&
                    v@ < childf.leastvar()
            }
        }
    }

    #[ghost]
    #[open(self)]
    #[requires(self.grows())]
    #[requires(self.is_valid_bdd(b))]
    #[ensures((^self).is_valid_bdd(b))]
    pub fn grows_is_valid_bdd(&mut self, b: Bdd<'arena>) {}

    #[ghost]
    #[open(self)]
    #[requires(self.grows())]
    #[requires(o.grows())]
    #[requires(^self == *o)]
    #[requires(*self == *oo && ^self == ^oo)]
    #[ensures(oo.grows())]
    pub fn grows_trans(&mut self, o: &mut Self, oo: &mut Self) {}

    #[ghost]
    #[requires(self.is_valid_bdd(a))]
    #[requires(x@ < a.leastvar())]
    #[ensures(a.interp(v) == a.interp(v.set(x, b)))]
    fn set_irrelevent_var(self, a: Bdd<'arena>, x: u64, v: Mapping<u64, bool>, b: bool) {
        pearlite! {
            match a {
                Bdd(&If { childt, childf, .. }, _) => {
                    self.set_irrelevent_var(childt, x, v, b);
                    self.set_irrelevent_var(childf, x, v, b);
                },
                _ => ()
            }
        }
    }

    #[ghost]
    #[requires(self.is_valid_bdd(a))]
    #[requires(self.is_valid_bdd(b))]
    #[requires(a != b)]
    #[ensures(a.interp(result) != b.interp(result))]
    #[variant(a.size() + b.size())]
    #[allow(path_statements)]
    fn discr_valuation(self, a: Bdd<'arena>, b: Bdd<'arena>) -> Mapping<u64, bool> {
        pearlite! {
            Self::set_irrelevent_var;
            if a.leastvar() < b.leastvar() {
                match a {
                    Bdd(&If { v, childt, childf }, _) =>
                        if childf != b {
                            self.discr_valuation(childf, b).set(v, false)
                        } else {
                            self.discr_valuation(childt, b).set(v, true)
                        },
                    _ => Mapping::cst(true)
                }
            } else if a.leastvar() > b.leastvar() {
                match b {
                    Bdd(&If { v, childt, childf }, _) =>
                        if childf != a {
                            self.discr_valuation(a, childf).set(v, false)
                        } else {
                            self.discr_valuation(a, childt).set(v, true)
                        },
                    _ => Mapping::cst(true)
                }
            } else {
                match a {
                    Bdd(&If { v, childt: childta, childf: childfa }, _) =>
                        match b {
                            Bdd(&If { childt: childtb, childf: childfb, .. }, _) =>
                                if childfa != childfb {
                                    self.discr_valuation(childfa, childfb).set(v, false)
                                } else {
                                    self.discr_valuation(childta, childtb).set(v, true)
                                },
                            _ => Mapping::cst(true)
                        },
                    _ => Mapping::cst(true)
                }
            }
        }
    }

    #[ghost]
    #[open(self)]
    #[requires(self.is_valid_bdd(a))]
    #[requires(self.is_valid_bdd(b))]
    #[requires(forall<v: _> a.interp(v) == b.interp(v))]
    #[ensures(a == b)]
    #[allow(path_statements)]
    pub fn bdd_canonical(self, a: Bdd<'arena>, b: Bdd<'arena>) {
        Self::discr_valuation;
    }
}

impl<'arena> Context<'arena> {
    pub fn new(alloc: &'arena bumpalo::Bump) -> Self {
        let t = &True; // FIXME: make it possible to write this is pearlite
        Context {
            alloc,
            hashcons: hashmap::MyHashMap::new(),
            hashcons_ghost: gh! { Mapping::cst(t) },
            not_memo: hashmap::MyHashMap::new(),
            and_memo: hashmap::MyHashMap::new(),
            cnt: 0,
        }
    }

    #[requires(self.is_valid_node(n))]
    #[ensures(*result.0 == n)]
    #[ensures(self.grows())]
    #[ensures((^self).is_valid_bdd(result))]
    fn hashcons(&mut self, n: Node<'arena>) -> Bdd<'arena> {
        if let Some(&r) = self.hashcons.get(&n) {
            proof_assert! { r.0@ == n@ };
            return r;
        }
        let r = Bdd(self.alloc.alloc(n), self.cnt);
        self.hashcons.add(n, r);
        self.hashcons_ghost = gh! { self.hashcons_ghost.set(r.1, r.0) };
        if self.cnt > u64::MAX - 1 {
            loop {
                // prevent self from being resolved
                self.cnt = self.cnt;
            }
        }
        self.cnt += 1;
        r
    }

    #[requires(self.is_valid_bdd(childt))]
    #[requires(self.is_valid_bdd(childf))]
    #[requires(x@ < childt.leastvar() && x@ < childf.leastvar())]
    #[ensures(self.grows())]
    #[ensures((^self).is_valid_bdd(result))]
    #[ensures(forall<v:_> result.interp(v) == if v.get(x) { childt.interp(v) } else { childf.interp(v) })]
    #[ensures(x@ <= result.leastvar())]
    fn node(&mut self, x: u64, childt: Bdd<'arena>, childf: Bdd<'arena>) -> Bdd<'arena> {
        if childt == childf {
            return childt;
        }
        self.hashcons(If { v: x, childt, childf })
    }

    #[ensures(self.grows())]
    #[ensures((^self).is_valid_bdd(result))]
    #[ensures(forall<v:_> result.interp(v))]
    #[ensures(u64::MAX@+1 == result.leastvar())]
    pub fn true_(&mut self) -> Bdd<'arena> {
        self.hashcons(True)
    }

    #[ensures(self.grows())]
    #[ensures((^self).is_valid_bdd(result))]
    #[ensures(forall<v:_> !result.interp(v))]
    #[ensures(u64::MAX@+1 == result.leastvar())]
    pub fn false_(&mut self) -> Bdd<'arena> {
        self.hashcons(False)
    }

    #[ensures(self.grows())]
    #[ensures((^self).is_valid_bdd(result))]
    #[ensures(forall<v:_> result.interp(v) == v.get(x))]
    pub fn v(&mut self, x: u64) -> Bdd<'arena> {
        let t = self.true_();
        let f = self.false_();
        self.node(x, t, f)
    }

    #[requires(self.is_valid_bdd(x))]
    #[ensures(self.grows())]
    #[ensures((^self).is_valid_bdd(result))]
    #[ensures(forall<v:_> result.interp(v) == !x.interp(v))]
    #[ensures(x.leastvar() <= result.leastvar())]
    #[variant(x.size())]
    pub fn not(&mut self, x: Bdd<'arena>) -> Bdd<'arena> {
        if let Some(r) = self.not_memo.get(&x) {
            return *r;
        }
        let r = match *x.0 {
            True => self.false_(),
            False => self.true_(),
            If { v, childt, childf } => {
                let childt = self.not(childt);
                let childf = self.not(childf);
                self.node(v, childt, childf)
            }
        };
        self.not_memo.add(x, r);
        r
    }

    #[requires(self.is_valid_bdd(a))]
    #[requires(self.is_valid_bdd(b))]
    #[ensures(self.grows())]
    #[ensures((^self).is_valid_bdd(result))]
    #[ensures(forall<v:_> result.interp(v) == (a.interp(v) && b.interp(v)))]
    #[ensures(a.leastvar() <= result.leastvar() || b.leastvar() <= result.leastvar())]
    #[variant(a.size() + b.size())]
    pub fn and(&mut self, a: Bdd<'arena>, b: Bdd<'arena>) -> Bdd<'arena> {
        if let Some(r) = self.and_memo.get(&(a, b)) {
            return *r;
        }
        let r = match (*a.0, *b.0) {
            (True, _) => b,
            (_, True) => a,
            (False, _) | (_, False) => self.false_(),
            (
                If { v: va, childt: childta, childf: childfa },
                If { v: vb, childt: childtb, childf: childfb },
            ) => {
                let (v, childt, childf);
                match va.cmp(&vb) {
                    Greater => {
                        v = vb;
                        childt = self.and(a, childtb);
                        childf = self.and(a, childfb);
                    }
                    Less => {
                        v = va;
                        childt = self.and(childta, b);
                        childf = self.and(childfa, b);
                    }
                    Equal => {
                        v = va;
                        childt = self.and(childta, childtb);
                        childf = self.and(childfa, childfb);
                    }
                }
                self.node(v, childt, childf)
            }
        };
        self.and_memo.add((a, b), r);
        r
    }
}
