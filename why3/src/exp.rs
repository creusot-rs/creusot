mod binder;

use crate::{Ident, Name, QName, declaration::Attribute, name, ty::Type};
use indexmap::IndexSet;
use std::collections::HashMap;

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

pub use self::binder::Binder;

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum BinOp {
    LogAnd,  // i.e., /\
    LogOr,   // i.e., \/
    LazyAnd, // i.e., &&
    LazyOr,  // i.e., ||
    Add,
    FloatAdd,
    Sub,
    FloatSub,
    Mul,
    FloatMul,
    Div,
    FloatDiv,
    Mod,
    Eq,
    FloatEq,
    Lt,
    FloatLt,
    Le,
    FloatLe,
    Gt,
    FloatGt,
    Ge,
    FloatGe,
    Ne,
}

impl BinOp {
    pub(crate) fn precedence(&self) -> Precedence {
        use Precedence::*;
        match self {
            BinOp::LogAnd => Conj,
            BinOp::LazyAnd => Conj,
            BinOp::LogOr => Disj,
            BinOp::LazyOr => Disj,
            BinOp::Add => Infix2,
            BinOp::Sub => Infix2,
            BinOp::Mul => Infix3,
            BinOp::Div => Infix3,
            BinOp::Mod => Infix3,
            BinOp::Eq => Infix1,
            BinOp::Lt => Infix1,
            BinOp::Le => Infix1,
            BinOp::Ne => Infix1,
            BinOp::Ge => Infix1,
            BinOp::Gt => Infix1,
            BinOp::FloatAdd => Infix4,
            BinOp::FloatSub => Infix4,
            BinOp::FloatMul => Infix4,
            BinOp::FloatDiv => Infix4,
            BinOp::FloatEq => Infix4,
            BinOp::FloatLt => Infix4,
            BinOp::FloatLe => Infix4,
            BinOp::FloatGt => Infix4,
            BinOp::FloatGe => Infix4,
        }
    }

    fn associative(&self) -> bool {
        matches!(
            self,
            BinOp::LogAnd | BinOp::LazyAnd | BinOp::LogOr | BinOp::LazyOr | BinOp::Add | BinOp::Mul
        )
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum UnOp {
    Not,
    Neg,
    FloatNeg,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
// TODO: multi-trigger/multiple triggers
pub struct Trigger(pub Box<[Exp]>);

impl Trigger {
    pub fn single(exp: Exp) -> Self {
        Trigger(Box::new([exp]))
    }
}

// TODO: Should we introduce an 'ExprKind' struct which wraps `Exp` with attributes?
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Exp {
    Let { pattern: Pattern, arg: Box<Exp>, body: Box<Exp> },
    Var(Name),
    Record { fields: Box<[(Name, Exp)]> },
    RecUp { record: Box<Exp>, updates: Box<[(Name, Exp)]> },
    RecField { record: Box<Exp>, label: Name },
    Tuple(Box<[Exp]>),
    Constructor { ctor: Name, args: Box<[Exp]> },
    // Function literals: `[| e1; e2; e3 |]` is shorthand for
    // `fun i -> if i = 0 then e1 else if i = 1 then e2 else e3`
    // It must be non-empty.
    FunLiteral(Box<[Exp]>),
    Const(Constant),
    BinaryOp(BinOp, Box<Exp>, Box<Exp>),
    UnaryOp(UnOp, Box<Exp>),
    Call(Box<Exp>, Box<[Exp]>),
    Attr(Attribute, Box<Exp>),
    Lam(Box<[Binder]>, Box<Exp>),

    Match(Box<Exp>, Box<[(Pattern, Exp)]>),
    IfThenElse(Box<Exp>, Box<Exp>, Box<Exp>),
    Ascribe(Box<Exp>, Type),
    // Predicates
    Impl(Box<Exp>, Box<Exp>),
    Forall(Box<[(Ident, Type)]>, Box<[Trigger]>, Box<Exp>),
    Exists(Box<[(Ident, Type)]>, Box<[Trigger]>, Box<Exp>),
}

pub trait ExpMutVisitor: Sized {
    fn visit_mut(&mut self, exp: &mut Exp) {
        super_visit_mut(self, exp)
    }

    fn visit_trigger_mut(&mut self, trig: &mut Trigger) {
        super_visit_mut_trigger(self, trig)
    }
}

pub fn super_visit_mut<T: ExpMutVisitor>(f: &mut T, exp: &mut Exp) {
    match exp {
        Exp::Let { pattern: _, arg, body } => {
            f.visit_mut(arg);
            f.visit_mut(body)
        }
        Exp::Var(_) => {}
        Exp::RecUp { record, updates } => {
            f.visit_mut(record);
            updates.iter_mut().for_each(|(_, val)| f.visit_mut(val));
        }
        Exp::RecField { record, label: _ } => f.visit_mut(record),
        Exp::Tuple(exps) => exps.iter_mut().for_each(|e| f.visit_mut(e)),
        Exp::Constructor { ctor: _, args } => args.iter_mut().for_each(|e| f.visit_mut(e)),
        Exp::FunLiteral(exps) => exps.iter_mut().for_each(|e| f.visit_mut(e)),
        Exp::Const(_) => {}
        Exp::BinaryOp(_, l, r) => {
            f.visit_mut(l);
            f.visit_mut(r)
        }
        Exp::UnaryOp(_, exp) => f.visit_mut(exp),
        Exp::Call(func, args) => {
            f.visit_mut(func);
            args.iter_mut().for_each(|e| f.visit_mut(e))
        }
        Exp::Lam(_, e) => f.visit_mut(e),
        Exp::Match(scrut, arms) => {
            f.visit_mut(scrut);
            arms.iter_mut().for_each(|(_, e)| f.visit_mut(e))
        }
        Exp::IfThenElse(c, l, r) => {
            f.visit_mut(c);
            f.visit_mut(l);
            f.visit_mut(r)
        }
        Exp::Ascribe(e, _) => f.visit_mut(e),
        Exp::Impl(l, r) => {
            f.visit_mut(l);
            f.visit_mut(r)
        }
        Exp::Forall(_, t, e) => {
            t.iter_mut().for_each(|t| f.visit_trigger_mut(t));
            f.visit_mut(e)
        }
        Exp::Exists(_, t, e) => {
            t.iter_mut().for_each(|t| f.visit_trigger_mut(t));
            f.visit_mut(e)
        }
        Exp::Attr(_, e) => f.visit_mut(e),
        Exp::Record { fields } => fields.iter_mut().for_each(|(_, e)| f.visit_mut(e)),
    }
}

pub fn super_visit_mut_trigger<T: ExpMutVisitor>(f: &mut T, trigger: &mut Trigger) {
    trigger.0.iter_mut().for_each(|t| f.visit_mut(t))
}

/// Capture-avoiding substitution
///
/// This is used as a persistent data structure:
/// we clone the `bound` whenever we add variables.
struct BoundSubst<'a> {
    /// The original substition. Remains constant during traversal.
    subst: &'a HashMap<Ident, Exp>,
    /// Renaming of bound variables to fresh names.
    bound: HashMap<Ident, Ident>,
}

impl<'a> ExpMutVisitor for BoundSubst<'a> {
    fn visit_mut(&mut self, exp: &mut Exp) {
        match exp {
            Exp::Var(Name::Local(v, suffix)) => {
                if let Some(w) = self.bound.get(v) {
                    *v = *w
                } else if let Some(e) = self.subst.get(v) {
                    if suffix.is_some() {
                        unimplemented!();
                    }
                    *exp = e.clone()
                }
            }
            Exp::Lam(binders, body) => {
                let mut bound = self.bound.clone();
                for binder in binders {
                    binder.refresh(&mut bound);
                }
                BoundSubst { bound, ..*self }.visit_mut(body);
            }
            Exp::Let { pattern, arg, body } => {
                self.visit_mut(arg);
                let mut bound = self.bound.clone();
                pattern.refresh(&mut bound);
                BoundSubst { bound, ..*self }.visit_mut(body);
            }
            Exp::Match(scrut, brs) => {
                self.visit_mut(scrut);
                for (pat, br) in brs {
                    let mut bound = self.bound.clone();
                    pat.refresh(&mut bound);
                    BoundSubst { bound, ..*self }.visit_mut(br);
                }
            }
            Exp::Forall(binders, trig, exp) => {
                let mut bound = self.bound.clone();
                for (id, _) in binders {
                    refresh_var(id, &mut bound);
                }
                let mut s = BoundSubst { bound, ..*self };
                trig.iter_mut().for_each(|t| s.visit_trigger_mut(t));
                s.visit_mut(exp);
            }
            Exp::Exists(binders, trig, exp) => {
                let mut bound = self.bound.clone();
                for (id, _) in binders {
                    refresh_var(id, &mut bound);
                }
                let mut s = BoundSubst { bound, ..*self };
                trig.iter_mut().for_each(|t| s.visit_trigger_mut(t));
                s.visit_mut(exp);
            }
            _ => super_visit_mut(self, exp),
        }
    }
}

pub trait ExpVisitor: Sized {
    fn visit(&mut self, exp: &Exp) {
        super_visit(self, exp)
    }

    fn visit_trigger(&mut self, trig: &Trigger) {
        super_visit_trigger(self, trig)
    }
}

pub fn super_visit<T: ExpVisitor>(f: &mut T, exp: &Exp) {
    match exp {
        Exp::Let { pattern: _, arg, body } => {
            f.visit(arg);
            f.visit(body)
        }
        Exp::Var(_) => {}
        Exp::RecUp { record, updates } => {
            f.visit(record);
            updates.iter().for_each(|(_, val)| f.visit(val));
        }
        Exp::RecField { record, label: _ } => f.visit(record),
        Exp::Tuple(exps) => exps.iter().for_each(|e| f.visit(e)),
        Exp::Constructor { ctor: _, args } => args.iter().for_each(|e| f.visit(e)),
        Exp::FunLiteral(exps) => exps.iter().for_each(|e| f.visit(e)),
        Exp::Const(_) => {}
        Exp::BinaryOp(_, l, r) => {
            f.visit(l);
            f.visit(r)
        }
        Exp::UnaryOp(_, exp) => f.visit(exp),
        Exp::Call(func, args) => {
            f.visit(func);
            args.iter().for_each(|e| f.visit(e))
        }
        Exp::Lam(_, e) => f.visit(e),
        Exp::Match(scrut, arms) => {
            f.visit(scrut);
            arms.iter().for_each(|(_, e)| f.visit(e))
        }
        Exp::IfThenElse(c, l, r) => {
            f.visit(c);
            f.visit(l);
            f.visit(r)
        }
        Exp::Ascribe(e, _) => f.visit(e),
        Exp::Impl(l, r) => {
            f.visit(l);
            f.visit(r)
        }
        Exp::Forall(_, t, e) => {
            t.iter().for_each(|t| f.visit_trigger(t));
            f.visit(e)
        }
        Exp::Exists(_, t, e) => {
            t.iter().for_each(|t| f.visit_trigger(t));
            f.visit(e)
        }
        Exp::Attr(_, e) => f.visit(e),
        Exp::Record { fields } => fields.iter().for_each(|(_, e)| f.visit(e)),
    }
}

pub fn super_visit_trigger<T: ExpVisitor>(f: &mut T, trigger: &Trigger) {
    trigger.0.iter().for_each(|t| f.visit(t))
}

impl Exp {
    pub fn boxed(self) -> Box<Self> {
        Box::new(self)
    }

    pub fn unit() -> Self {
        Exp::Tuple(Box::new([]))
    }

    pub fn var(ident: Ident) -> Self {
        Exp::Var(Name::local(ident))
    }

    pub fn qvar(q: QName) -> Self {
        Exp::Var(Name::Global(q))
    }

    pub fn lazy_conj(l: Exp, r: Exp) -> Self {
        l.lazy_and(r)
    }

    pub fn not(self) -> Self {
        Exp::UnaryOp(UnOp::Not, Box::new(self))
    }

    pub fn eq(self, rhs: Self) -> Self {
        if self.is_true() {
            rhs
        } else if rhs.is_true() {
            self
        } else {
            Exp::BinaryOp(BinOp::Eq, Box::new(self), Box::new(rhs))
        }
    }

    pub fn neq(self, rhs: Self) -> Self {
        Exp::BinaryOp(BinOp::Ne, Box::new(self), Box::new(rhs))
    }

    pub fn app(self, args: impl IntoIterator<Item = Self>) -> Self {
        let args: Box<[Exp]> = args.into_iter().collect();
        if args.is_empty() { self } else { Exp::Call(Box::new(self), args) }
    }

    pub fn field(self, label: Name) -> Self {
        Self::RecField { record: Box::new(self), label }
    }

    pub fn match_(self, branches: impl IntoIterator<Item = (Pattern, Exp)>) -> Self {
        Exp::Match(Box::new(self), branches.into_iter().collect())
    }

    pub fn lazy_and(self, other: Self) -> Self {
        if self.is_true() {
            other
        } else if other.is_true() {
            self
        } else {
            Exp::BinaryOp(BinOp::LazyAnd, Box::new(self), Box::new(other))
        }
    }

    pub fn log_and(self, other: Self) -> Self {
        if self.is_true() {
            other
        } else if other.is_true() {
            self
        } else {
            Exp::BinaryOp(BinOp::LogAnd, Box::new(self), Box::new(other))
        }
    }

    pub fn log_or(self, other: Self) -> Self {
        if self.is_true() {
            self
        } else if other.is_true() {
            other
        } else {
            Exp::BinaryOp(BinOp::LogOr, Box::new(self), Box::new(other))
        }
    }

    pub fn if_(cond: Self, then: Self, else_: Self) -> Self {
        if (then.is_true() && else_.is_true()) || cond.is_true() {
            then
        } else if cond.is_false() {
            else_
        } else {
            Exp::IfThenElse(Box::new(cond), Box::new(then), Box::new(else_))
        }
    }

    /// Build an implication
    ///
    /// Performs the following simplifications
    /// - `true -> A` -> `A`
    /// - `A -> true` -> `true`
    pub fn implies(self, other: Self) -> Self {
        if self.is_true() || other.is_true() {
            other
        } else {
            Exp::Impl(Box::new(self), Box::new(other))
        }
    }

    /// Builds a quantifier with explicit trigger
    ///
    /// Simplfies `∀ x, true` into `true`
    pub fn forall_trig(
        bound: impl IntoIterator<Item = (Ident, Type)>,
        trigger: impl IntoIterator<Item = Trigger>,
        body: Exp,
    ) -> Self {
        let mut bound = bound.into_iter().peekable();
        if body.is_true() || bound.peek().is_none() {
            body
        } else {
            Exp::Forall(bound.collect(), trigger.into_iter().collect(), Box::new(body))
        }
    }

    /// Builds a quantifier
    ///
    /// Simplifies `∀ x, true` into `true`
    pub fn forall(bound: impl IntoIterator<Item = (Ident, Type)>, body: Exp) -> Self {
        Exp::forall_trig(bound, [], body)
    }

    pub fn exists_trig(
        bound: impl IntoIterator<Item = (Ident, Type)>,
        trigger: impl IntoIterator<Item = Trigger>,
        body: Exp,
    ) -> Self {
        let mut bound = bound.into_iter().peekable();
        if body.is_false() || bound.peek().is_none() {
            body
        } else {
            Exp::Exists(bound.collect(), trigger.into_iter().collect(), Box::new(body))
        }
    }

    pub fn exists(bound: impl IntoIterator<Item = (Ident, Type)>, body: Exp) -> Self {
        Exp::exists_trig(bound, [], body)
    }

    pub fn with_attr(self, attr: Attribute) -> Self {
        Exp::Attr(attr, Box::new(self))
    }

    pub fn is_true(&self) -> bool {
        if let Exp::Const(Constant::Bool(true)) = self {
            true
        } else if let Exp::Attr(_, e) = self {
            e.is_true()
        } else {
            false
        }
    }

    pub fn is_false(&self) -> bool {
        if let Exp::Const(Constant::Bool(false)) = self {
            true
        } else if let Exp::Attr(_, e) = self {
            e.is_false()
        } else {
            false
        }
    }

    pub fn mk_true() -> Self {
        Exp::Const(Constant::const_true())
    }

    pub fn mk_false() -> Self {
        Exp::Const(Constant::const_false())
    }

    pub fn int(i: i128) -> Self {
        Exp::Const(Constant::Int(i, None))
    }

    pub fn let_(id: impl Into<Ident>, arg: Exp, mut body: Exp) -> Exp {
        let ident = id.into();
        let occurences = body.occurences();

        if !occurences.contains_key(&ident) {
            body
        // Remove this if performance is a concern
        } else if occurences[&ident] == 1 {
            body.subst(&mut [(ident, arg)].into_iter().collect());
            body
        } else {
            Exp::Let { pattern: Pattern::VarP(ident), arg: Box::new(arg), body: Box::new(body) }
        }
    }

    /// Returns a type abscribtion expression (e.g. `(1: int)`), of the form `(self: ty)`.
    pub fn ascribe(self, ty: Type) -> Self {
        Exp::Ascribe(Box::new(self), ty)
    }

    pub fn uint(value: u128) -> Self {
        Exp::Const(Constant::Uint(value, None))
    }

    /// Reorder binary operations, so that the one that are associative are always evaluated left-to-right.
    ///
    /// # Example
    ///
    /// `1 + (2 + 3)` becomes `(1 + 2) + 3`.
    pub fn reassociate(&mut self) {
        struct Reassociate;

        impl ExpMutVisitor for Reassociate {
            fn visit_mut(&mut self, exp: &mut Exp) {
                match exp {
                    Exp::BinaryOp(op, l, r) if op.associative() => {
                        let mut reordered = false;
                        match op.precedence().associativity().unwrap() {
                            AssocDir::Left => {
                                //     self                self
                                //   /       \            /    \
                                //   l        r    =>    r     rr
                                //           / \        / \
                                //          rl rr      l  rl
                                //
                                // First swap rl and rr
                                // Then swap the left child of with the left child of self moving `l` into
                                // the left chid of `r` and moving `rr` to the left of self
                                // Finally swap the two children of self which are now `r` and `rr`
                                if let Exp::BinaryOp(iop, rl, rr) = &mut **r {
                                    if *iop == *op {
                                        std::mem::swap(rl, rr);
                                        std::mem::swap(rl, l);
                                        std::mem::swap(l, r);
                                        reordered = true;
                                    }
                                }
                            }
                            AssocDir::Right => {
                                // ll -> l, r -> lr, lr -> ll, l -> r;
                                if let Exp::BinaryOp(iop, ll, lr) = &mut **l {
                                    if *iop == *op {
                                        std::mem::swap(ll, lr);
                                        std::mem::swap(lr, r);
                                        std::mem::swap(l, r);
                                        reordered = true;
                                    }
                                }
                            }
                        }
                        if reordered {
                            self.visit_mut(exp);
                        } else {
                            self.visit_mut(l);
                            self.visit_mut(r);
                        }
                    }
                    _ => super_visit_mut(self, exp),
                }
            }
        }
        Reassociate.visit_mut(self);
    }
}

/// Precedence ordered from lowest to highest priority
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Precedence {
    /// if then else / let in
    IfLet,
    Attr,
    Cast,
    Impl,     // -> / <-> / by / so
    Disj,     // \/ / ||
    Conj,     // /\ / &&
    Not,      // not
    Infix1,   // infix-op level 1 (right-assoc)
    Infix2,   // infix-op level 2 (left-assoc)
    Infix3,   // infix-op level 3 (left-assoc)
    Infix4,   // infix-op level 4 (left-assoc)
    Prefix,   // prefix-op
    Abs,      // Function abstraction
    App,      // Function application
    Field,    // Record field accesses (from observing the why3 parser)
    Brackets, // Brackets ([_])
    Atom,     // Syntactically closed or atomic expressions
    BangOp,   // !
}

#[derive(PartialEq, Debug)]
pub enum AssocDir {
    Left,
    Right,
}

impl Precedence {
    pub fn next(&self) -> Self {
        match self {
            Precedence::IfLet => Precedence::Attr,
            Precedence::Attr => Precedence::Cast,
            Precedence::Cast => Precedence::Impl,
            Precedence::Impl => Precedence::Disj,
            Precedence::Disj => Precedence::Conj,
            Precedence::Conj => Precedence::Not,
            Precedence::Not => Precedence::Infix1,
            Precedence::Infix1 => Precedence::Infix2,
            Precedence::Infix2 => Precedence::Infix3,
            Precedence::Infix3 => Precedence::Infix4,
            Precedence::Infix4 => Precedence::Prefix,
            Precedence::Prefix => Precedence::Abs,
            Precedence::Abs => Precedence::App,
            Precedence::App => Precedence::Field,
            Precedence::Field => Precedence::Brackets,
            Precedence::Brackets => Precedence::Atom,
            Precedence::Atom => Precedence::BangOp,
            Precedence::BangOp => Precedence::BangOp,
        }
    }

    pub fn associativity(&self) -> Option<AssocDir> {
        use Precedence::*;
        match self {
            Infix1 => None,
            Infix2 | Infix3 => Some(AssocDir::Left),
            Conj => Some(AssocDir::Right),
            Disj => Some(AssocDir::Right),
            App => Some(AssocDir::Left),
            Abs => Some(AssocDir::Right),
            _ => None,
        }
    }
}

impl Exp {
    pub fn associativity(&self) -> Option<AssocDir> {
        self.precedence().associativity()
    }

    pub(crate) fn precedence(&self) -> Precedence {
        use Precedence::*;

        match self {
            Exp::Let { .. } => IfLet,
            Exp::Lam(_, _) => Abs,
            Exp::Var(_) => Atom,
            Exp::RecUp { .. } => App,
            Exp::RecField { .. } => Field,
            Exp::Tuple(_) => Atom,
            Exp::Constructor { .. } => App,
            Exp::FunLiteral(_) => Atom,
            Exp::Match(_, _) => Abs,
            Exp::IfThenElse(_, _, _) => IfLet,
            Exp::Const(_) => Atom,
            Exp::UnaryOp(UnOp::Neg | UnOp::FloatNeg, _) => Prefix,
            Exp::UnaryOp(UnOp::Not, _) => Not,
            Exp::BinaryOp(op, _, _) => op.precedence(),
            Exp::Call(_, _) => App,
            Exp::Impl(_, _) => Impl,
            Exp::Forall(_, _, _) => IfLet,
            Exp::Exists(_, _, _) => IfLet,
            Exp::Ascribe(_, _) => Cast,
            Exp::Attr(_, _) => Attr,
            Exp::Record { fields: _ } => Atom,
        }
    }

    /// Returns `true` if `id` appears in `self` not under a binder.
    ///
    /// # Examples
    ///
    /// - `self = a + 1`, `id = a` -> `true`
    /// - `self = a + 1`, `id = b` -> `false`
    /// - `self = ∀b, a + b`, `id = a` -> `true`
    /// - `self = ∀b, a + b`, `id = b` -> `false`
    pub fn occurs(&self, id: &Ident) -> bool {
        let fvs = self.occurences();

        fvs.contains_key(id)
    }

    fn occurences(&self) -> HashMap<Ident, u64> {
        struct Occurs {
            occurs: HashMap<Ident, u64>,
        }

        impl ExpVisitor for Occurs {
            fn visit(&mut self, exp: &Exp) {
                match exp {
                    Exp::Var(Name::Local(v, _)) => {
                        *self.occurs.entry(v.clone()).or_insert(0) += 1;
                    }
                    Exp::Let { pattern, arg, body } => {
                        let mut occurs = std::mem::take(&mut self.occurs);
                        self.visit(body);
                        pattern.binders().iter().for_each(|p| {
                            self.occurs.remove(p);
                        });

                        self.visit(arg);
                        occurs.drain().for_each(|(k, v)| *self.occurs.entry(k).or_insert(0) += v);
                    }
                    Exp::Forall(bnds, trig, exp) => {
                        let mut fvs = std::mem::take(&mut self.occurs);
                        self.visit(exp);
                        trig.iter().for_each(|t| self.visit_trigger(t));
                        bnds.iter().for_each(|(l, _)| {
                            self.occurs.remove(l);
                        });
                        fvs.drain().for_each(|(k, v)| *self.occurs.entry(k).or_insert(0) += v);
                    }
                    Exp::Exists(bnds, trig, exp) => {
                        let mut fvs = std::mem::take(&mut self.occurs);
                        self.visit(exp);
                        trig.iter().for_each(|t| self.visit_trigger(t));
                        bnds.iter().for_each(|(l, _)| {
                            self.occurs.remove(l);
                        });
                        fvs.drain().for_each(|(k, v)| *self.occurs.entry(k).or_insert(0) += v);
                    }
                    _ => super_visit(self, exp),
                }
            }
        }

        let mut fvs = Occurs { occurs: Default::default() };
        fvs.visit(self);
        fvs.occurs
    }

    /// Get the free variables in `self`.
    pub fn fvs(&self) -> IndexSet<Ident> {
        self.occurences().into_keys().collect()
    }

    pub fn qfvs(&self) -> IndexSet<QName> {
        struct QFvs {
            qfvs: IndexSet<QName>,
        }

        impl ExpVisitor for QFvs {
            fn visit(&mut self, exp: &Exp) {
                match exp {
                    Exp::Var(Name::Global(v)) => {
                        self.qfvs.insert(v.clone());
                    }
                    _ => super_visit(self, exp),
                }
            }
        }

        let mut qfvs = QFvs { qfvs: IndexSet::new() };

        qfvs.visit(self);

        qfvs.qfvs
    }

    /// Substituate free variables of `self` by their value in `subst`.
    pub fn subst(&mut self, subst: &HashMap<Ident, Exp>) {
        BoundSubst { subst, bound: HashMap::new() }.visit_mut(self);
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Constant {
    Int(i128, Option<Type>),
    Uint(u128, Option<Type>),
    Float(f64, Option<Type>),
    String(String),
    Other(String),
    Bool(bool),
    Char(char, Type),
}

impl From<Constant> for Exp {
    fn from(val: Constant) -> Self {
        Exp::Const(val)
    }
}

impl Constant {
    pub fn const_true() -> Self {
        Constant::Bool(true)
    }
    pub fn const_false() -> Self {
        Constant::Bool(false)
    }
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Pattern {
    Wildcard,
    VarP(Ident),
    TupleP(Box<[Pattern]>),
    ConsP(Name, Box<[Pattern]>),
    RecP(Box<[(Name, Pattern)]>),
}

impl Pattern {
    pub fn mk_true() -> Self {
        Self::ConsP(Name::Global(QName { module: Box::new([]), name: *name::TRUE }), Box::new([]))
    }

    pub fn mk_false() -> Self {
        Self::ConsP(Name::Global(QName { module: Box::new([]), name: *name::FALSE }), Box::new([]))
    }

    pub fn binders(&self) -> IndexSet<Ident> {
        match self {
            Pattern::Wildcard => IndexSet::new(),
            Pattern::VarP(s) => {
                let mut b = IndexSet::new();
                b.insert(s.clone());
                b
            }
            Pattern::TupleP(pats) => {
                pats.iter().map(|p| p.binders()).fold(IndexSet::new(), |mut set, x| {
                    set.extend(x);
                    set
                })
            }
            Pattern::ConsP(_, args) => {
                args.iter().map(|p| p.binders()).fold(IndexSet::new(), |mut set, x| {
                    set.extend(x);
                    set
                })
            }
            Pattern::RecP(vec) => {
                vec.iter().map(|(_, p)| p.binders()).fold(IndexSet::new(), |mut set, x| {
                    set.extend(x);
                    set
                })
            }
        }
    }

    pub fn refresh(&mut self, bound: &mut HashMap<Ident, Ident>) {
        match self {
            Pattern::Wildcard => {}
            Pattern::VarP(id) => refresh_var(id, bound),
            Pattern::TupleP(pats) => {
                pats.iter_mut().for_each(|p| p.refresh(bound));
            }
            Pattern::ConsP(_, pats) => {
                pats.iter_mut().for_each(|p| p.refresh(bound));
            }
            Pattern::RecP(fields) => {
                fields.iter_mut().for_each(|(_, p)| p.refresh(bound));
            }
        }
    }
}

pub(crate) fn refresh_var(id: &mut Ident, bound: &mut HashMap<Ident, Ident>) {
    let id2 = id.refresh();
    bound.insert(*id, id2);
    *id = id2;
}
