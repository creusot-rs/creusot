use std::collections::HashMap;

use crate::{declaration::Attribute, ty::Type, Ident, QName};
use indexmap::IndexSet;

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

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
        match self {
            BinOp::LogAnd => true,
            BinOp::LazyAnd => true,
            BinOp::LogOr => true,
            BinOp::LazyOr => true,
            BinOp::Add => true,
            BinOp::Mul => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum UnOp {
    Not,
    Neg,
    FloatNeg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub(crate) enum Purity {
    Logic,
    Program,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
// TODO: multi-trigger/multiple triggers
pub struct Trigger(pub Vec<Exp>);

impl Trigger {
    pub fn single(exp: Exp) -> Self {
        Trigger(vec![exp])
    }
}

// TODO: Should we introduce an 'ExprKind' struct which wraps `Exp` with attributes?
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Exp {
    Assert(Box<Exp>),
    Assume(Box<Exp>),
    Any(Type),
    // TODO: Remove
    Current(Box<Exp>),
    // TODO: Remove
    Final(Box<Exp>),
    Let {
        pattern: Pattern,
        arg: Box<Exp>,
        body: Box<Exp>,
    },
    Var(Ident),
    QVar(QName),
    Record {
        fields: Vec<(String, Exp)>,
    },
    RecUp {
        record: Box<Exp>,
        updates: Vec<(String, Exp)>,
    },
    RecField {
        record: Box<Exp>,
        label: String,
    },
    Tuple(Vec<Exp>),
    Constructor {
        ctor: QName,
        args: Vec<Exp>,
    },
    Const(Constant),
    BinaryOp(BinOp, Box<Exp>, Box<Exp>),
    UnaryOp(UnOp, Box<Exp>),
    Call(Box<Exp>, Vec<Exp>),
    Verbatim(String),
    Attr(Attribute, Box<Exp>),
    Ghost(Box<Exp>),
    /// Lambda abstraction
    Abs(Vec<Binder>, Box<Exp>),
    /// Expression (statement) sequencing (aka ;)
    Chain(Vec<Exp>),

    Match(Box<Exp>, Vec<(Pattern, Exp)>),
    IfThenElse(Box<Exp>, Box<Exp>, Box<Exp>),
    Ascribe(Box<Exp>, Type),
    Pure(Box<Exp>),
    // Predicates
    Old(Box<Exp>),
    Absurd,
    Impl(Box<Exp>, Box<Exp>),
    Forall(Vec<(Ident, Type)>, Vec<Trigger>, Box<Exp>),
    Exists(Vec<(Ident, Type)>, Vec<Trigger>, Box<Exp>),
    FnLit(Box<Exp>),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Binder {
    Wild,                           // let f _ = ..
    UnNamed(Type),                  // let f int : bool = ..
    Named(Ident),                   // let f a  = ..
    Typed(bool, Vec<Binder>, Type), // let f (ghost? a int b : int) = ..
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
        Exp::Any(_) => {}
        Exp::Current(e) => f.visit_mut(e),
        Exp::Final(e) => f.visit_mut(e),
        Exp::Let { pattern: _, arg, body } => {
            f.visit_mut(arg);
            f.visit_mut(body)
        }
        Exp::Var(_) => {}
        Exp::QVar(_) => {}
        Exp::RecUp { record, updates } => {
            f.visit_mut(record);
            updates.iter_mut().for_each(|(_, val)| f.visit_mut(val));
        }
        Exp::RecField { record, label: _ } => f.visit_mut(record),
        Exp::Tuple(exps) => exps.iter_mut().for_each(|e| f.visit_mut(e)),
        Exp::Constructor { ctor: _, args } => args.iter_mut().for_each(|e| f.visit_mut(e)),
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
        Exp::Verbatim(_) => {}
        Exp::Abs(_, e) => f.visit_mut(e),
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
        Exp::Pure(e) => f.visit_mut(e),
        Exp::Old(e) => f.visit_mut(e),
        Exp::Absurd => {}
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
        Exp::Ghost(e) => f.visit_mut(e),
        Exp::Record { fields } => fields.iter_mut().for_each(|(_, e)| f.visit_mut(e)),
        Exp::Chain(fields) => fields.iter_mut().for_each(|e| f.visit_mut(e)),
        Exp::FnLit(e) => f.visit_mut(e),
        Exp::Assert(e) => f.visit_mut(e),
        Exp::Assume(e) => f.visit_mut(e),
    }
}

pub fn super_visit_mut_trigger<T: ExpMutVisitor>(f: &mut T, trigger: &mut Trigger) {
    trigger.0.iter_mut().for_each(|t| f.visit_mut(t))
}

impl<'a> ExpMutVisitor for &'a HashMap<Ident, Exp> {
    fn visit_mut(&mut self, exp: &mut Exp) {
        match exp {
            Exp::Var(v) => {
                if let Some(e) = self.get(v) {
                    *exp = e.clone()
                }
            }
            Exp::Abs(binders, body) => {
                let mut subst = self.clone();

                for binder in binders {
                    binder.fvs().into_iter().for_each(|id| {
                        subst.remove(&id);
                    });
                }

                let mut s = &subst;
                s.visit_mut(body);
            }

            Exp::Let { pattern, arg, body } => {
                self.visit_mut(arg);
                let mut bound = pattern.binders();
                let mut subst = self.clone();
                bound.drain(..).for_each(|k| {
                    subst.remove(&k);
                });

                let mut s = &subst;
                s.visit_mut(body);
            }
            Exp::Match(scrut, brs) => {
                self.visit_mut(scrut);

                for (pat, br) in brs {
                    let mut s = self.clone();
                    pat.binders().drain(..).for_each(|b| {
                        s.remove(&b);
                    });

                    let mut s = &s;
                    s.visit_mut(br);
                }
            }
            Exp::Forall(binders, trig, exp) => {
                let mut subst = self.clone();
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });
                let bnds: IndexSet<_> = binders.iter().map(|b| &b.0).cloned().collect();
                let mut extended = HashMap::new();
                for (_, exp) in &mut subst {
                    for id in &bnds & &exp.fvs() {
                        extended.insert(id.clone(), Exp::var(format!("{}'", &*id)));
                    }
                }
                binders.iter_mut().for_each(|(id, _)| {
                    if extended.contains_key(id) {
                        *id = format!("{}'", &**id).into();
                    }
                });
                subst.extend(extended);

                let mut s = &subst;
                s.visit_mut(exp);
                trig.iter_mut().for_each(|t| s.visit_trigger_mut(t));
            }
            Exp::Exists(binders, trig, exp) => {
                let mut subst = self.clone();
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });
                let bnds: IndexSet<_> = binders.iter().map(|b| &b.0).cloned().collect();
                let mut extended = HashMap::new();
                for (_, exp) in &mut subst {
                    for id in &bnds & &exp.fvs() {
                        extended.insert(id.clone(), Exp::var(format!("{}'", &*id)));
                    }
                }
                binders.iter_mut().for_each(|(id, _)| {
                    if extended.contains_key(id) {
                        *id = format!("{}'", &**id).into();
                    }
                });
                subst.extend(extended);

                let mut s = &subst;
                s.visit_mut(exp);
                trig.iter_mut().for_each(|t| s.visit_trigger_mut(t));
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
        Exp::Any(_) => {}
        Exp::Current(e) => f.visit(e),
        Exp::Final(e) => f.visit(e),
        Exp::Let { pattern: _, arg, body } => {
            f.visit(arg);
            f.visit(body)
        }
        Exp::Var(_) => {}
        Exp::QVar(_) => {}
        Exp::RecUp { record, updates } => {
            f.visit(record);
            updates.iter().for_each(|(_, val)| f.visit(val));
        }
        Exp::RecField { record, label: _ } => f.visit(record),
        Exp::Tuple(exps) => exps.iter().for_each(|e| f.visit(e)),
        Exp::Constructor { ctor: _, args } => args.iter().for_each(|e| f.visit(e)),
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
        Exp::Verbatim(_) => {}
        Exp::Abs(_, e) => f.visit(e),
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
        Exp::Pure(e) => f.visit(e),
        Exp::Old(e) => f.visit(e),
        Exp::Absurd => {}
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
        Exp::Ghost(e) => f.visit(e),
        Exp::Record { fields } => fields.iter().for_each(|(_, e)| f.visit(e)),
        Exp::Chain(fields) => fields.iter().for_each(|e| f.visit(e)),
        Exp::FnLit(e) => f.visit(e),
        Exp::Assert(e) => f.visit(e),
        Exp::Assume(e) => f.visit(e),
    }
}

pub fn super_visit_trigger<T: ExpVisitor>(f: &mut T, trigger: &Trigger) {
    trigger.0.iter().for_each(|t| f.visit(t))
}

impl Exp {
    pub fn qvar(q: QName) -> Self {
        Exp::QVar(q)
    }

    pub fn var(v: impl Into<Ident>) -> Self {
        Exp::Var(v.into())
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

    pub fn lt(self, rhs: Self) -> Self {
        Exp::BinaryOp(BinOp::Lt, Box::new(self), Box::new(rhs))
    }

    pub fn leq(self, rhs: Self) -> Self {
        Exp::BinaryOp(BinOp::Le, Box::new(self), Box::new(rhs))
    }

    pub fn app(mut self, arg: Vec<Self>) -> Self {
        match self {
            Exp::Call(_, ref mut args) => args.extend(arg),
            _ => self = Exp::Call(Box::new(self), arg),
        }
        self
    }

    // Construct an application from this expression and an argument
    pub fn app_to(mut self, arg: Self) -> Self {
        match self {
            Exp::Call(_, ref mut args) => args.push(arg),
            _ => self = Exp::Call(Box::new(self), vec![arg]),
        }
        self
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
        if then.is_true() && else_.is_true() {
            then
        } else if cond.is_true() {
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
    /// - True -> A <-> A
    /// - A -> True <-> True
    pub fn implies(self, other: Self) -> Self {
        if self.is_true() {
            other
        } else if other.is_true() {
            other
        } else {
            Exp::Impl(Box::new(self), Box::new(other))
        }
    }

    /// Builds a quantifier with explicit trigger
    ///
    /// Simplfies ∀ x, True into True
    pub fn forall_trig(bound: Vec<(Ident, Type)>, trigger: Vec<Trigger>, body: Exp) -> Self {
        if body.is_true() {
            body
        } else {
            Exp::Forall(bound, trigger, Box::new(body))
        }
    }

    /// Builds a quantifier
    ///
    /// Simplfies ∀ x, True into True
    pub fn forall(bound: Vec<(Ident, Type)>, body: Exp) -> Self {
        Exp::forall_trig(bound, Vec::new(), body)
    }

    pub fn exists_trig(bound: Vec<(Ident, Type)>, trigger: Vec<Trigger>, body: Exp) -> Self {
        Exp::Exists(bound, trigger, Box::new(body))
    }

    pub fn exists(bound: Vec<(Ident, Type)>, body: Exp) -> Self {
        Exp::exists_trig(bound, Vec::new(), body)
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

    pub fn ascribe(self, ty: Type) -> Self {
        Exp::Ascribe(Box::new(self), ty)
    }

    pub fn uint(value: u128) -> Self {
        Exp::Const(Constant::Uint(value, None))
    }

    pub fn is_pure(&self) -> bool {
        struct IsPure {
            pure: bool,
        }

        impl ExpVisitor for IsPure {
            fn visit(&mut self, exp: &Exp) {
                match exp {
                    Exp::Verbatim(_) => self.pure &= false,
                    Exp::Absurd => self.pure &= false,
                    // This is a bit absurd, but you can't put "pure {...}"
                    // in a term, so it's not "pure".
                    Exp::Pure(_) => self.pure &= false,
                    Exp::Assert(_) => self.pure &= false,
                    _ => {
                        super_visit(self, exp);
                    }
                }
            }
        }

        let mut p = IsPure { pure: true };
        p.visit(self);
        p.pure
    }

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

// Precedence ordered from lowest to highest priority
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Precedence {
    IfLet, // if then else / let in
    Attr,
    Cast,
    Impl,   // -> / <-> / by / so
    Disj,   // \/ / ||
    Conj,   // /\ / &&
    Not,    // not
    Infix1, // infix-op level 1 (right-assoc)
    AtOld,
    Infix2,   // infix-op level 2 (left-assoc)
    Infix3,   // infix-op level 3 (left-assoc)
    Infix4,   // infix-op level 4 (left-assoc)
    Prefix,   // prefix-op
    Abs,      // Function abstraction
    App,      // Function application
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
            Precedence::Infix1 => Precedence::AtOld,
            Precedence::AtOld => Precedence::Infix2,
            Precedence::Infix2 => Precedence::Infix3,
            Precedence::Infix3 => Precedence::Infix4,
            Precedence::Infix4 => Precedence::Prefix,
            Precedence::Prefix => Precedence::Abs,
            Precedence::Abs => Precedence::App,
            Precedence::App => Precedence::Brackets,
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
            Exp::Current(_) => Prefix,
            Exp::Final(_) => Prefix,
            Exp::Let { .. } => IfLet,
            Exp::Abs(_, _) => Abs,
            Exp::Var(_) => Atom,
            Exp::QVar(_) => Atom,
            Exp::RecUp { .. } => App,
            Exp::RecField { .. } => Infix4,
            Exp::Tuple(_) => Atom,
            Exp::Constructor { .. } => App,
            // Exp::Seq(_, _) => { Term }
            Exp::Match(_, _) => Abs,
            Exp::IfThenElse(_, _, _) => IfLet,
            Exp::Const(_) => Atom,
            Exp::UnaryOp(UnOp::Neg | UnOp::FloatNeg, _) => Prefix,
            Exp::UnaryOp(UnOp::Not, _) => Not,
            Exp::BinaryOp(op, _, _) => op.precedence(),
            Exp::Call(_, _) => App,
            // Exp::Verbatim(_) => Any,
            Exp::Impl(_, _) => Impl,
            Exp::Forall(_, _, _) => IfLet,
            Exp::Exists(_, _, _) => IfLet,
            Exp::Ascribe(_, _) => Cast,
            Exp::Absurd => Atom,
            Exp::Pure(_) => Atom,
            Exp::Old(_) => AtOld,
            Exp::Any(_) => Prefix,
            Exp::Verbatim(_) => Atom,
            Exp::Attr(_, _) => Attr,
            Exp::Ghost(_) => App,
            Exp::Record { fields: _ } => Atom,
            // TODO: Wrong, should introduce a better name for it
            Exp::Chain(_) => Attr,
            Exp::FnLit(_) => Atom,
            Exp::Assert(_) => Atom,
            Exp::Assume(_) => Atom,
            // _ => unimplemented!("{:?}", self),
        }
    }

    pub fn occurs(&self, id: &Ident) -> bool {
        let fvs = self.occurences();

        fvs.contains_key(id)
    }

    pub fn occurences(&self) -> HashMap<Ident, u64> {
        struct Occurs {
            occurs: HashMap<Ident, u64>,
        }

        impl ExpVisitor for Occurs {
            fn visit(&mut self, exp: &Exp) {
                match exp {
                    Exp::Var(v) => {
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
                    Exp::QVar(v) => {
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

    pub fn subst(&mut self, subst: &mut Environment) {
        subst.visit_mut(self);
    }
}

#[derive(Default)]
pub struct Environment {
    substs: Vec<HashMap<Ident, Exp>>,
}

impl Environment {
    pub fn add_subst(&mut self, substs: HashMap<Ident, Exp>) {
        self.substs.push(substs);
    }

    pub fn pop_subst(&mut self) {
        self.substs.pop();
    }

    pub fn get(&self, id: &Ident) -> Option<Exp> {
        for sub in self.substs.iter().rev() {
            if let Some(e) = sub.get(id) {
                return Some(e.clone());
            }
        }
        None
    }

    pub fn occ(&self, id: &Ident) -> usize {
        let mut occ = 0;
        for sub in self.substs.iter() {
            if sub.get(id).is_some() {
                occ += 1;
            }
        }

        occ
    }
}

impl FromIterator<(Ident, Exp)> for Environment {
    fn from_iter<T: IntoIterator<Item = (Ident, Exp)>>(iter: T) -> Self {
        Environment { substs: vec![iter.into_iter().collect()] }
    }
}

impl ExpMutVisitor for Environment {
    fn visit_mut(&mut self, exp: &mut Exp) {
        match exp {
            Exp::Var(v) => {
                if let Some(e) = self.get(v) {
                    *exp = e.clone()
                }
            }
            Exp::Abs(binders, body) => {
                let mut bound_here = HashMap::default();

                for binder in binders {
                    binder.fvs().into_iter().for_each(|id| {
                        bound_here.insert(id.clone(), Exp::var(id));
                    });
                }

                self.add_subst(bound_here);
                self.visit_mut(body);
                self.pop_subst();
            }

            Exp::Let { pattern, arg, body } => {
                self.visit_mut(arg);

                let mut bound = pattern.binders();

                let mut bound_here = HashMap::default();
                bound.drain(..).for_each(|k| {
                    bound_here.insert(k.clone(), Exp::var(k));
                });

                self.add_subst(bound_here);
                self.visit_mut(body);
                self.pop_subst();
            }
            Exp::Match(scrut, brs) => {
                self.visit_mut(scrut);

                for (pat, br) in brs {
                    let mut bound_here = HashMap::default();
                    pat.binders().drain(..).for_each(|k| {
                        bound_here.insert(k.clone(), Exp::var(k));
                    });

                    self.add_subst(bound_here);
                    self.visit_mut(br);
                    self.pop_subst();
                }
            }
            Exp::Forall(binders, trig, exp) => {
                let mut bound_here = HashMap::default();

                binders.iter().for_each(|k| {
                    bound_here.insert(k.0.clone(), Exp::var(k.0.clone()));
                });

                self.add_subst(bound_here);
                self.visit_mut(exp);
                trig.iter_mut().for_each(|t| self.visit_trigger_mut(t));
                self.pop_subst();
            }
            Exp::Exists(binders, trig, exp) => {
                let mut bound_here = HashMap::default();

                binders.iter().for_each(|k| {
                    bound_here.insert(k.0.clone(), Exp::var(k.0.clone()));
                });

                self.add_subst(bound_here);
                self.visit_mut(exp);
                trig.iter_mut().for_each(|t| self.visit_trigger_mut(t));
                self.pop_subst();
            }
            _ => super_visit_mut(self, exp),
        }
    }

    fn visit_trigger_mut(&mut self, trig: &mut Trigger) {
        super_visit_mut_trigger(self, trig)
    }
}

impl Binder {
    pub fn typed(id: Ident, ty: Type) -> Self {
        Binder::Typed(false, vec![Binder::Named(id)], ty)
    }

    pub fn ghost(id: Ident, ty: Type) -> Self {
        Binder::Typed(true, vec![Binder::Named(id)], ty)
    }

    pub fn wild(ty: Type) -> Self {
        Binder::Typed(false, vec![Binder::Wild], ty)
    }

    pub fn fvs(&self) -> Vec<Ident> {
        match self {
            Binder::Wild => Vec::new(),
            Binder::UnNamed(_) => Vec::new(),
            Binder::Named(id) => vec![id.clone()],
            Binder::Typed(_, ids, _) => ids.iter().fold(Vec::new(), |mut acc, id| {
                acc.extend(id.fvs());
                acc
            }),
        }
    }

    fn flatten_inner(self, ty: &Type, out: &mut Vec<(Ident, Type)>) {
        match self {
            Binder::Wild => out.push(("_".into(), ty.clone())),
            Binder::UnNamed(_) => out.push(("_".into(), ty.clone())),
            Binder::Named(id) => out.push((id, ty.clone())),
            Binder::Typed(_, ids, ty2) => {
                assert!(ty == &ty2);
                ids.into_iter().for_each(|i| i.flatten_inner(ty, out))
            }
        }
    }

    pub fn var_type_pairs(self) -> Vec<(Ident, Type)> {
        if let Binder::Typed(_, _, ty) = &self {
            let mut out = Vec::new();
            let ty = &ty.clone();
            self.flatten_inner(ty, &mut out);
            out
        } else {
            panic!("cannot get name and type for binder")
        }
    }

    pub fn type_of(&self) -> Option<&Type> {
        match self {
            Binder::Wild => None,
            Binder::UnNamed(_) => None,
            Binder::Named(_) => None,
            Binder::Typed(_, _, ty) => Some(ty),
        }
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
    TupleP(Vec<Pattern>),
    ConsP(QName, Vec<Pattern>),
    // RecP(String, String),
}

impl Pattern {
    pub fn mk_true() -> Self {
        Self::ConsP(QName { module: vec![], name: "True".into() }, vec![])
    }

    pub fn mk_false() -> Self {
        Self::ConsP(QName { module: vec![], name: "False".into() }, vec![])
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
        }
    }
}
