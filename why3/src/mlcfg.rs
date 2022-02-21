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
        match self {
            Exp::Current(e) => e.is_pure(),
            Exp::Final(e) => e.is_pure(),
            Exp::Let { arg, body, .. } => arg.is_pure() && body.is_pure(),
            Exp::Var(_, Purity::Logic) => true,
            Exp::Var(_, Purity::Program) => false,
            Exp::QVar(_, Purity::Logic) => true,
            Exp::QVar(_, Purity::Program) => false,
            Exp::RecUp { record, val, .. } => record.is_pure() && val.is_pure(),
            Exp::RecField { record, .. } => record.is_pure(),
            Exp::Tuple(args) => args.iter().all(Exp::is_pure),
            Exp::Constructor { args, .. } => args.iter().all(Exp::is_pure),
            Exp::BorrowMut(e) => e.is_pure(),
            Exp::Const(_) => true,
            Exp::BinaryOp(_, l, r) => l.is_pure() && r.is_pure(),
            Exp::UnaryOp(_, e) => e.is_pure(),
            Exp::Call(f, args) => f.is_pure() && args.iter().all(Exp::is_pure),
            Exp::Verbatim(_) => false,
            Exp::Abs(_, e) => e.is_pure(),
            Exp::Match(e, brs) => e.is_pure() && brs.iter().all(|(_, e)| e.is_pure()),
            Exp::IfThenElse(s, i, e) => s.is_pure() && i.is_pure() && e.is_pure(),
            Exp::Ascribe(e, _) => e.is_pure(),
            Exp::Absurd => false,
            Exp::Impl(l, r) => l.is_pure() && r.is_pure(),
            Exp::Forall(_, e) => e.is_pure(),
            Exp::Exists(_, e) => e.is_pure(),
            Exp::Pure(_) => true,
            Exp::Old(e) => e.is_pure(),
        }
    }

    pub fn reassociate(&mut self) {
        match self {
            Exp::Current(e) => e.reassociate(),
            Exp::Final(e) => e.reassociate(),
            Exp::Let { arg, body, .. } => {
                arg.reassociate();
                body.reassociate()
            }
            Exp::Var(_, _) => (),
            Exp::QVar(_, _) => (),
            Exp::RecUp { val, record, .. } => {
                record.reassociate();
                val.reassociate()
            }
            Exp::RecField { record, .. } => record.reassociate(),
            Exp::Tuple(fields) => fields.iter_mut().for_each(|f| f.reassociate()),
            Exp::Constructor { args, .. } => args.iter_mut().for_each(|f| f.reassociate()),
            Exp::BorrowMut(e) => e.reassociate(),
            Exp::Const(_) => (),
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
                    self.reassociate();
                } else {
                    l.reassociate();
                    r.reassociate();
                }
            }
            Exp::UnaryOp(_, e) => e.reassociate(),
            Exp::Call(f, args) => {
                f.reassociate();
                args.iter_mut().for_each(|a| a.reassociate())
            }
            Exp::Verbatim(_) => (),
            Exp::Abs(_, e) => e.reassociate(),
            Exp::Match(e, brs) => {
                e.reassociate();
                brs.iter_mut().for_each(|(_, e)| e.reassociate())
            }
            Exp::IfThenElse(s, i, e) => {
                s.reassociate();
                i.reassociate();
                e.reassociate();
            }
            Exp::Ascribe(e, _) => e.reassociate(),
            Exp::Absurd => (),
            Exp::Impl(l, r) => {
                l.reassociate();
                r.reassociate()
            }
            Exp::Forall(_, e) => e.reassociate(),
            Exp::Exists(_, e) => e.reassociate(),
            Exp::Pure(e) => e.reassociate(),
            Exp::Old(e) => e.reassociate(),
        }
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
    Infix2, // infix-op level 2 (left-assoc)
    Infix3, // infix-op level 3 (left-assoc)
    // Infix4, // infix-op level 4 (left-assoc)
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
            Precedence::Infix3 => Precedence::Prefix,
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
            // Exp::RecField { .. } => Any,
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
        match self {
            Exp::Current(e) => e.fvs(),
            Exp::Final(e) => e.fvs(),
            Exp::Let { pattern, arg, body } => {
                let bound = pattern.binders();

                &(&body.fvs() - &bound) | &arg.fvs()
            }
            Exp::Var(v, _) => {
                let mut fvs = IndexSet::new();
                fvs.insert(v.clone());
                fvs
            }
            Exp::QVar(_, _) => IndexSet::new(),
            // Exp::RecUp { record, label, val } => {}
            // Exp::Tuple(_) => {}
            Exp::Constructor { ctor: _, args } => {
                args.iter().fold(IndexSet::new(), |acc, v| &acc | &v.fvs())
            }
            Exp::Const(_) => IndexSet::new(),
            Exp::BinaryOp(_, l, r) => &l.fvs() | &r.fvs(),
            Exp::Call(f, args) => args.iter().fold(f.fvs(), |acc, a| &acc | &a.fvs()),
            Exp::Impl(h, c) => &h.fvs() | &c.fvs(),
            Exp::Forall(bnds, exp) => bnds.iter().fold(exp.fvs(), |mut acc, (l, _)| {
                acc.remove(l);
                acc
            }),
            Exp::BorrowMut(e) => e.fvs(),
            Exp::Verbatim(_) => IndexSet::new(),
            Exp::Pure(e) => e.fvs(),
            _ => unimplemented!(),
        }
    }

    pub fn qfvs(&self) -> IndexSet<QName> {
        match self {
            Exp::Current(e) => e.qfvs(),
            Exp::Final(e) => e.qfvs(),
            Exp::Let { arg, body, .. } => &body.qfvs() | &arg.qfvs(),
            Exp::Var(_, _) => IndexSet::new(),
            Exp::QVar(v, _) => {
                let mut fvs = IndexSet::new();
                fvs.insert(v.clone());
                fvs
            }
            Exp::Constructor { ctor: _, args } => {
                args.iter().fold(IndexSet::new(), |acc, v| &acc | &v.qfvs())
            }
            Exp::Const(_) => IndexSet::new(),
            Exp::BinaryOp(_, l, r) => &l.qfvs() | &r.qfvs(),
            Exp::Call(f, args) => args.iter().fold(f.qfvs(), |acc, a| &acc | &a.qfvs()),
            Exp::Impl(h, c) => &h.qfvs() | &c.qfvs(),
            Exp::Forall(_, exp) => exp.qfvs(),
            Exp::Exists(_, exp) => exp.qfvs(),
            Exp::BorrowMut(e) => e.qfvs(),
            Exp::Verbatim(_) => IndexSet::new(),
            Exp::Tuple(args) => args.iter().fold(IndexSet::new(), |acc, v| &acc | &v.qfvs()),
            Exp::Match(scrut, brs) => {
                brs.iter().fold(scrut.qfvs(), |acc, (_, br)| &acc | &br.qfvs())
            }
            Exp::IfThenElse(s, i, e) => &(&s.qfvs() | &i.qfvs()) | &e.qfvs(),
            Exp::Absurd => IndexSet::new(),
            Exp::Pure(e) => e.qfvs(),
            _ => unimplemented!("qvfs: {:?}", self),
        }
    }

    pub fn subst(&mut self, subst: &HashMap<Ident, Exp>) {
        match self {
            Exp::Current(e) => e.subst(subst),
            Exp::Final(e) => e.subst(subst),
            Exp::Let { pattern, arg, body } => {
                arg.subst(subst);
                let mut bound = pattern.binders();
                let mut subst = subst.clone();
                bound.drain(..).for_each(|k| {
                    subst.remove(&k);
                });

                body.subst(&subst);
            }
            Exp::Var(v, _) => {
                if let Some(e) = subst.get(v) {
                    *self = e.clone()
                }
            }
            Exp::RecUp { record, val, .. } => {
                record.subst(subst);
                val.subst(subst);
            }
            Exp::RecField { record, .. } => {
                record.subst(subst);
            }
            Exp::Tuple(tuple) => {
                for t in tuple {
                    t.subst(subst);
                }
            }
            Exp::Constructor { args, .. } => {
                for a in args {
                    a.subst(subst);
                }
            }
            Exp::Abs(ident, body) => {
                let mut subst = subst.clone();
                subst.remove(ident);
                body.subst(&subst);
            }
            Exp::Match(box scrut, brs) => {
                scrut.subst(subst);

                for (pat, br) in brs {
                    let mut s = subst.clone();
                    pat.binders().drain(..).for_each(|b| {
                        s.remove(&b);
                    });
                    br.subst(&s);
                }
            }
            Exp::IfThenElse(s, i, e) => {
                s.subst(subst);
                i.subst(subst);
                e.subst(subst);
            }
            Exp::BorrowMut(e) => e.subst(subst),
            Exp::UnaryOp(_, o) => {
                o.subst(subst);
            }
            Exp::BinaryOp(_, l, r) => {
                l.subst(subst);
                r.subst(subst)
            }
            Exp::Impl(hyp, exp) => {
                hyp.subst(subst);
                exp.subst(subst)
            }
            Exp::Forall(binders, exp) => {
                let mut subst = subst.clone();
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });
                exp.subst(&subst);
            }
            Exp::Exists(binders, exp) => {
                let mut subst = subst.clone();
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });
                exp.subst(&subst);
            }
            Exp::Call(_, a) => {
                for arg in a {
                    arg.subst(subst);
                }
            }
            Exp::Ascribe(e, _) => e.subst(subst),
            Exp::Pure(e) => e.subst(subst),
            Exp::QVar(_, _) => {}
            Exp::Const(_) => {}
            Exp::Verbatim(_) => {}
            Exp::Absurd => {}
            Exp::Old(e) => e.subst(subst),
        }
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
