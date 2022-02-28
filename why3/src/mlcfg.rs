use indexmap::IndexSet;
use std::collections::HashMap;

use crate::*;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

pub mod printer;

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct BlockId(pub usize);

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Terminator {
    Goto(BlockId),
    Absurd,
    Return,
    Switch(Exp, Vec<(Pattern, Terminator)>),
}

impl Terminator {
    pub fn retarget(&mut self, from: BlockId, to: BlockId) {
        match self {
            Self::Goto(id) if *id == from => *id = to,
            Self::Switch(_, brs) => brs.iter_mut().for_each(|(_, t)| t.retarget(from, to)),
            _ => {}
        }
    }

    pub fn is_goto(&self) -> bool {
        matches!(self, Self::Goto(..))
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Statement {
    Assign { lhs: Ident, rhs: Exp },
    Invariant(Ident, Exp),
    Assume(Exp),
    Assert(Exp),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Type {
    Bool,
    Char,
    Integer,
    MutableBorrow(Box<Type>),
    TVar(Ident),
    TConstructor(QName),
    TApp(Box<Type>, Vec<Type>),
    Tuple(Vec<Type>),
    TFun(Box<Type>, Box<Type>),
}

impl Type {
    pub fn predicate(ty: Self) -> Self {
        Self::TFun(box ty, box Self::Bool)
    }

    fn complex(&self) -> bool {
        use Type::*;
        !matches!(self, Bool | Char | Integer | TVar(_) | Tuple(_) | TConstructor(_))
    }

    pub(crate) fn find_used_types(&self, tys: &mut IndexSet<QName>) {
        use Type::*;

        match self {
            MutableBorrow(t) => t.find_used_types(tys),
            TConstructor(qn) => {
                tys.insert(qn.clone());
            }
            TApp(f, args) => {
                f.find_used_types(tys);
                args.iter().for_each(|arg| arg.find_used_types(tys));
            }
            Tuple(args) => {
                args.iter().for_each(|arg| arg.find_used_types(tys));
            }
            TFun(a, b) => {
                a.find_used_types(tys);
                b.find_used_types(tys);
            }
            _ => (),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum BinOp {
    And,
    Or,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Ne,
}

impl BinOp {
    fn precedence(&self) -> Precedence {
        use Precedence::*;
        match self {
            BinOp::And => Conj,
            BinOp::Or => Disj,
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
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Purity {
    Logic,
    Program,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Exp {
    Current(Box<Exp>),
    Final(Box<Exp>),
    Let { pattern: Pattern, arg: Box<Exp>, body: Box<Exp> },
    Var(Ident, Purity),
    QVar(QName, Purity),
    RecUp { record: Box<Exp>, label: String, val: Box<Exp> },
    RecField { record: Box<Exp>, label: String },
    Tuple(Vec<Exp>),
    Constructor { ctor: QName, args: Vec<Exp> },
    BorrowMut(Box<Exp>),
    Const(Constant),
    BinaryOp(BinOp, Box<Exp>, Box<Exp>),
    UnaryOp(UnOp, Box<Exp>),
    Call(Box<Exp>, Vec<Exp>),
    Verbatim(String),
    // Seq(Box<Exp>, Box<Exp>),
    Abs(Ident, Box<Exp>),
    Match(Box<Exp>, Vec<(Pattern, Exp)>),
    IfThenElse(Box<Exp>, Box<Exp>, Box<Exp>),
    Ascribe(Box<Exp>, Type),
    Pure(Box<Exp>),
    // Predicates
    Old(Box<Exp>),
    Absurd,
    Impl(Box<Exp>, Box<Exp>),
    Forall(Vec<(Ident, Type)>, Box<Exp>),
    Exists(Vec<(Ident, Type)>, Box<Exp>),
}

pub trait ExpMutVisitor: Sized {
    fn visit_mut(&mut self, exp: &mut Exp) {
        super_visit_mut(self, exp)
    }
}

pub fn super_visit_mut<T: ExpMutVisitor>(f: &mut T, exp: &mut Exp) {
    match exp {
        Exp::Current(e) => f.visit_mut(e),
        Exp::Final(e) => f.visit_mut(e),
        Exp::Let { pattern: _, arg, body } => {
            f.visit_mut(arg);
            f.visit_mut(body)
        }
        Exp::Var(_, _) => {}
        Exp::QVar(_, _) => {}
        Exp::RecUp { record, label: _, val } => {
            f.visit_mut(record);
            f.visit_mut(val)
        }
        Exp::RecField { record, label: _ } => f.visit_mut(record),
        Exp::Tuple(exps) => exps.iter_mut().for_each(|e| f.visit_mut(e)),
        Exp::Constructor { ctor: _, args } => args.iter_mut().for_each(|e| f.visit_mut(e)),
        Exp::BorrowMut(e) => f.visit_mut(e),
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
        Exp::Forall(_, e) => f.visit_mut(e),
        Exp::Exists(_, e) => f.visit_mut(e),
    }
}

pub trait ExpVisitor: Sized {
    fn visit(&mut self, exp: &Exp) {
        super_visit(self, exp)
    }
}

pub fn super_visit<T: ExpVisitor>(f: &mut T, exp: &Exp) {
    match exp {
        Exp::Current(e) => f.visit(e),
        Exp::Final(e) => f.visit(e),
        Exp::Let { pattern: _, arg, body } => {
            f.visit(arg);
            f.visit(body)
        }
        Exp::Var(_, _) => {}
        Exp::QVar(_, _) => {}
        Exp::RecUp { record, label: _, val } => {
            f.visit(record);
            f.visit(val)
        }
        Exp::RecField { record, label: _ } => f.visit(record),
        Exp::Tuple(exps) => exps.iter().for_each(|e| f.visit(e)),
        Exp::Constructor { ctor: _, args } => args.iter().for_each(|e| f.visit(e)),
        Exp::BorrowMut(e) => f.visit(e),
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
        Exp::Forall(_, e) => f.visit(e),
        Exp::Exists(_, e) => f.visit(e),
    }
}

impl Exp {
    pub fn impure_qvar(q: QName) -> Self {
        Exp::QVar(q, Purity::Program)
    }

    pub fn impure_var(v: Ident) -> Self {
        Exp::Var(v, Purity::Program)
    }

    pub fn pure_qvar(q: QName) -> Self {
        Exp::QVar(q, Purity::Logic)
    }

    pub fn pure_var(v: Ident) -> Self {
        Exp::Var(v, Purity::Logic)
    }

    pub fn conj(l: Exp, r: Exp) -> Self {
        Exp::BinaryOp(BinOp::And, box l, box r)
    }

    pub fn mk_true() -> Self {
        Exp::Const(Constant::const_true())
    }

    pub fn mk_false() -> Self {
        Exp::Const(Constant::const_false())
    }

    pub fn is_pure(&self) -> bool {
        struct IsPure {
            pure: bool,
        }

        impl ExpVisitor for IsPure {
            fn visit(&mut self, exp: &Exp) {
                match exp {
                    Exp::Var(_, Purity::Program) => self.pure &= false,
                    Exp::QVar(_, Purity::Program) => self.pure &= false,
                    Exp::Verbatim(_) => self.pure &= false,
                    Exp::Absurd => self.pure &= false,
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
                    Exp::BinaryOp(op, l, r) => {
                        let mut reordered = false;
                        match op.precedence().associativity() {
                            Some(AssocDir::Left) => {
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
                                if let box Exp::BinaryOp(iop, rl, rr) = r {
                                    if *iop == *op {
                                        std::mem::swap(rl, rr);
                                        std::mem::swap(rl, l);
                                        std::mem::swap(l, r);
                                        reordered = true;
                                    }
                                }
                            }
                            Some(AssocDir::Right) => {
                                // ll -> l, r -> lr, lr -> ll, l -> r;
                                if let box Exp::BinaryOp(iop, ll, lr) = l {
                                    if *iop == *op {
                                        std::mem::swap(ll, lr);
                                        std::mem::swap(lr, r);
                                        std::mem::swap(l, r);
                                        reordered = true;
                                    }
                                }
                            }
                            None => {}
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
enum Precedence {
    IfLet, // if then else / let in
    // Attr,
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
            Precedence::IfLet => Precedence::Cast,
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
    fn precedence(&self) -> Precedence {
        use Precedence::*;

        match self {
            Exp::Current(_) => Prefix,
            Exp::Final(_) => Prefix,
            Exp::Let { .. } => IfLet,
            Exp::Abs(_, _) => Abs,
            Exp::Var(_, _) => Atom,
            Exp::QVar(_, _) => Atom,
            Exp::RecUp { .. } => App,
            Exp::RecField { .. } => Infix4,
            Exp::Tuple(_) => Atom,
            Exp::Constructor { .. } => App,
            // Exp::Seq(_, _) => { Term }
            Exp::Match(_, _) => Atom,
            Exp::IfThenElse(_, _, _) => IfLet,
            Exp::BorrowMut(_) => App,
            Exp::Const(_) => Atom,
            Exp::UnaryOp(UnOp::Neg, _) => Prefix,
            Exp::UnaryOp(UnOp::Not, _) => BangOp,
            Exp::BinaryOp(op, _, _) => op.precedence(),
            Exp::Call(_, _) => App,
            // Exp::Verbatim(_) => Any,
            Exp::Impl(_, _) => Impl,
            Exp::Forall(_, _) => IfLet,
            Exp::Exists(_, _) => IfLet,
            Exp::Ascribe(_, _) => Cast,
            Exp::Absurd => Atom,
            Exp::Pure(_) => Atom,
            Exp::Old(_) => AtOld,
            _ => unimplemented!("{:?}", self),
        }
    }

    pub fn fvs(&self) -> IndexSet<Ident> {
        struct Fvs {
            fvs: IndexSet<Ident>,
        }

        impl ExpVisitor for Fvs {
            fn visit(&mut self, exp: &Exp) {
                match exp {
                    Exp::Var(v, _) => {
                        self.fvs.insert(v.clone());
                    }
                    Exp::Let { pattern, arg, body } => {
                        let fvs = std::mem::take(&mut self.fvs);
                        self.visit(body);
                        self.fvs = (&self.fvs) - &pattern.binders();
                        self.visit(arg);
                        self.fvs.extend(fvs);
                    }
                    Exp::Forall(bnds, exp) => {
                        let fvs = std::mem::take(&mut self.fvs);
                        self.visit(exp);

                        bnds.iter().for_each(|(l, _)| {
                            self.fvs.remove(l);
                        });
                        self.fvs.extend(fvs);
                    }
                    Exp::Exists(bnds, exp) => {
                        let fvs = std::mem::take(&mut self.fvs);
                        self.visit(exp);

                        bnds.iter().for_each(|(l, _)| {
                            self.fvs.remove(l);
                        });
                        self.fvs.extend(fvs);
                    }
                    _ => super_visit(self, exp),
                }
            }
        }

        let mut fvs = Fvs { fvs: IndexSet::new() };
        fvs.visit(self);
        fvs.fvs
    }

    pub fn qfvs(&self) -> IndexSet<QName> {
        struct QFvs {
            qfvs: IndexSet<QName>,
        }

        impl ExpVisitor for QFvs {
            fn visit(&mut self, exp: &Exp) {
                match exp {
                    Exp::QVar(v, _) => {
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

    pub fn subst(&mut self, mut subst: &HashMap<Ident, Exp>) {
        impl<'a> ExpMutVisitor for &'a HashMap<Ident, Exp> {
            fn visit_mut(&mut self, exp: &mut Exp) {
                match exp {
                    Exp::Var(v, _) => {
                        if let Some(e) = self.get(v) {
                            *exp = e.clone()
                        }
                    }
                    Exp::Abs(ident, body) => {
                        let mut subst = self.clone();
                        subst.remove(ident);
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
                    Exp::Match(box scrut, brs) => {
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
                    Exp::Forall(binders, exp) => {
                        let mut subst = self.clone();
                        binders.iter().for_each(|k| {
                            subst.remove(&k.0);
                        });
                        let mut s = &subst;
                        s.visit_mut(exp);
                    }
                    Exp::Exists(binders, exp) => {
                        let mut subst = self.clone();
                        binders.iter().for_each(|k| {
                            subst.remove(&k.0);
                        });
                        let mut s = &subst;
                        s.visit_mut(exp);
                    }
                    _ => super_visit_mut(self, exp),
                }
            }
        }
        subst.visit_mut(self);
    }

    // Construct an application from this expression and an argument
    pub fn app_to(mut self, arg: Self) -> Self {
        match self {
            Exp::Call(_, ref mut args) => args.push(arg),
            _ => self = Exp::Call(box self, vec![arg]),
        }
        self
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Constant {
    Int(i128, Option<Type>),
    Uint(u128, Option<Type>),
    // Float(f64),
    Other(String),
}
impl Constant {
    pub fn const_true() -> Self {
        Constant::Other("true".to_owned())
    }
    pub fn const_false() -> Self {
        Constant::Other("false".to_owned())
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
