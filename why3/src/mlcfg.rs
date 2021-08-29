use indexmap::IndexSet;
use std::collections::HashMap;
use std::fmt::Display;

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

pub mod printer;

pub fn drop_fix() -> QName {
    QName { module: vec![], name: "drop_fix".into() }
}
pub fn drop_uint() -> QName {
    QName { module: vec![], name: "drop_uint".into() }
}
pub fn drop_int() -> QName {
    QName { module: vec![], name: "drop_int".into() }
}
pub fn drop_float() -> QName {
    QName { module: vec![], name: "drop_float".into() }
}
pub fn drop_bool() -> QName {
    QName { module: vec![], name: "drop_bool".into() }
}
pub fn drop_mut_ref() -> QName {
    QName { module: vec![], name: "drop_mut_ref".into() }
}
pub fn drop_ref() -> QName {
    QName { module: vec![], name: "drop_ref".into() }
}

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
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Statement {
    Assign { lhs: LocalIdent, rhs: Exp },
    Invariant(String, Exp),
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
    TVar(String),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum LocalIdent {
    /// A MIR local along with an optional human-readable name
    Anon(usize, Option<String>),

    /// A local variable,
    Name(String),
}

impl From<&str> for LocalIdent {
    fn from(s: &str) -> Self {
        Self::Name(s.to_owned())
    }
}

impl From<String> for LocalIdent {
    fn from(s: String) -> Self {
        Self::Name(s)
    }
}

impl From<LocalIdent> for Exp {
    fn from(li: LocalIdent) -> Self {
        Exp::Var(li)
    }
}

impl Display for LocalIdent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocalIdent::Anon(l, n) => {
                if let Some(n) = n {
                    write!(f, "{}", n)?;
                }
                write!(f, "_{:?}", l)
            }
            LocalIdent::Name(nm) => write!(f, "{}", nm),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct QName {
    pub module: Vec<String>,
    pub name: String,
}

impl QName {
    pub fn name(&self) -> String {
        self.name.clone()
    }

    pub fn module_name(mut self) -> QName {
        let name = self.module.pop().unwrap();

        QName { module: self.module, name }
    }

    pub fn from_string(s: &str) -> Option<QName> {
        let mut chunks = s.split('.');

        let name = chunks.next_back()?;
        let module = chunks.map(|s| s.into()).collect();

        Some(QName { module, name: name.into() })
    }
}

impl From<&str> for QName {
    fn from(nm: &str) -> Self {
        QName { module: vec![], name: nm.to_string() }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum BinOp {
    And,
    Or,
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Ne,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Exp {
    Current(Box<Exp>),
    Final(Box<Exp>),
    Let { pattern: Pattern, arg: Box<Exp>, body: Box<Exp> },
    Var(LocalIdent),
    QVar(QName),
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
    Abs(LocalIdent, Box<Exp>),
    Match(Box<Exp>, Vec<(Pattern, Exp)>),

    // Predicates
    Absurd,
    Impl(Box<Exp>, Box<Exp>),
    Forall(Vec<(LocalIdent, Type)>, Box<Exp>),
    Exists(Vec<(LocalIdent, Type)>, Box<Exp>),
}

impl Exp {
    pub fn conj(l: Exp, r: Exp) -> Self {
        Exp::BinaryOp(BinOp::And, box l, box r)
    }

    pub fn mk_true() -> Self {
        Exp::Const(Constant::const_true())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Closed,
    Any,
    Let,
    Assign,
    Impl,
    Or,
    And,
    Compare,
    AddSub,
    Mul,
    PrefixOp,
    Term,
    Call,
}

impl Exp {
    fn precedence(&self) -> Precedence {
        use Precedence::*;

        match self {
            Exp::Current(_) => PrefixOp,
            Exp::Final(_) => PrefixOp,
            Exp::Let { .. } => Let,
            Exp::Abs(_, _) => Let,
            Exp::Var(_) => Closed,
            Exp::QVar(_) => Closed,
            Exp::RecUp { .. } => Term,
            Exp::RecField { .. } => Any,
            Exp::Tuple(_) => Closed,
            Exp::Constructor { .. } => Term,
            // Exp::Seq(_, _) => { Term }
            Exp::Match(_, _) => Term,
            Exp::BorrowMut(_) => Term,
            Exp::Const(_) => Closed,
            Exp::UnaryOp(UnOp::Neg, _) => PrefixOp,
            Exp::UnaryOp(UnOp::Not, _) => Call,
            Exp::BinaryOp(op, _, _) => match op {
                BinOp::And => And,
                BinOp::Or => Or,
                BinOp::Add => AddSub,
                BinOp::Sub => AddSub,
                BinOp::Mul => Mul,
                BinOp::Div => Term,
                BinOp::Eq => Compare,
                BinOp::Lt => Compare,
                BinOp::Le => Compare,
                BinOp::Ne => Compare,
                BinOp::Ge => Compare,
                BinOp::Gt => Compare,
            },
            Exp::Call(_, _) => Call,
            Exp::Verbatim(_) => Any,
            Exp::Impl(_, _) => Impl,
            Exp::Forall(_, _) => Any,
            Exp::Exists(_, _) => Any,
            Exp::Absurd => Closed,
        }
    }

    pub fn fvs(&self) -> IndexSet<LocalIdent> {
        match self {
            Exp::Current(e) => e.fvs(),
            Exp::Final(e) => e.fvs(),
            Exp::Let { pattern, arg, body } => {
                let bound = pattern.binders();

                &(&body.fvs() - &bound) | &arg.fvs()
            }
            Exp::Var(v) => {
                let mut fvs = IndexSet::new();
                fvs.insert(v.clone());
                fvs
            }
            Exp::QVar(_) => IndexSet::new(),
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
            _ => unimplemented!(),
        }
    }

    pub fn qfvs(&self) -> IndexSet<QName> {
        match self {
            Exp::Current(e) => e.qfvs(),
            Exp::Final(e) => e.qfvs(),
            Exp::Let { arg, body, .. } => &body.qfvs() | &arg.qfvs(),
            Exp::Var(_) => IndexSet::new(),
            Exp::QVar(v) => {
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
            Exp::Absurd => IndexSet::new(),
            _ => unimplemented!("qvfs: {:?}", self),
        }
    }

    pub fn subst(&mut self, subst: &HashMap<LocalIdent, Exp>) {
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
            Exp::Var(v) => {
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
            Exp::QVar(_) => {}
            Exp::Const(_) => {}
            Exp::Verbatim(_) => {}
            Exp::Absurd => {}
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
    VarP(LocalIdent),
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

    pub fn binders(&self) -> IndexSet<LocalIdent> {
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
