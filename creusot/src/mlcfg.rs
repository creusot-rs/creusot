use std::collections::HashSet;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Display;

// Imports related to MLCfg Constatns
pub use mir::{BinOp, UnOp};
use rustc_middle::{
    mir,
    ty::{print::FmtPrinter, print::PrettyPrinter, TyCtxt},
};

use rustc_hir::def::Namespace;
use rustc_middle::mir::{BasicBlock, Local};

pub mod printer;

pub const PRELUDE: &str = include_str!("prelude.mlw");

pub fn drop_fix() -> QName {
    QName { module: vec![], name: vec!["drop_fix".into()] }
}
pub fn drop_uint() -> QName {
    QName { module: vec![], name: vec!["drop_uint".into()] }
}
pub fn drop_int() -> QName {
    QName { module: vec![], name: vec!["drop_int".into()] }
}
pub fn drop_float() -> QName {
    QName { module: vec![], name: vec!["drop_float".into()] }
}
pub fn drop_bool() -> QName {
    QName { module: vec![], name: vec!["drop_bool".into()] }
}
pub fn drop_mut_ref() -> QName {
    QName { module: vec![], name: vec!["drop_mut_ref".into()] }
}
pub fn drop_ref() -> QName {
    QName { module: vec![], name: vec!["drop_ref".into()] }
}

#[derive(Default)]
pub struct Module {
    pub decls: Vec<Decl>,
}

pub enum Decl {
    FunDecl(Function),
    // TyDecl(TyDecl),
    // PredDecl(Predicate),
}

#[derive(Debug)]
pub struct Function {
    pub name: QName,
    pub retty: Type,
    pub args: Vec<(LocalIdent, Type)>,
    pub vars: Vec<(LocalIdent, Type)>,
    pub blocks: BTreeMap<BlockId, Block>,
    pub preconds: Vec<String>, // for now we blindly pass contracts down
    pub postconds: Vec<String>,
}

#[derive(Debug)]
pub struct Predicate {
    pub name: QName,
    pub args: Vec<(LocalIdent, Type)>,
    pub body: Exp,
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct BlockId(usize);

impl From<&BasicBlock> for BlockId {
    fn from(b: &BasicBlock) -> Self {
        BlockId((*b).into())
    }
}
impl From<BasicBlock> for BlockId {
    fn from(b: BasicBlock) -> Self {
        BlockId(b.into())
    }
}

#[derive(Debug)]
pub enum Terminator {
    Goto(BlockId),
    Absurd,
    Return,
    Switch(Exp, Vec<(Pattern, Terminator)>),
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assign { lhs: LocalIdent, rhs: Exp },
    Invariant(String, Exp),
    Assume(Exp),
}

#[derive(Debug, Clone)]
pub enum Type {
    Bool,
    Char,
    Int(rustc_ast::ast::IntTy),
    Uint(rustc_ast::ast::UintTy),
    Float(rustc_ast::ast::FloatTy),
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
        !matches!(self, Bool | Char | Int(_) | Uint(_) | TVar(_) | Tuple(_) | TConstructor(_))
    }

    fn find_used_types(&self, tys: &mut HashSet<QName>) {
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

#[derive(Debug)]
pub struct TyDecl {
    pub ty_name: QName,
    pub ty_params: Vec<String>,
    pub ty_constructors: Vec<(String, Vec<Type>)>,
}

impl TyDecl {
    pub fn used_types(&self) -> HashSet<QName> {
        let mut used = HashSet::new();
        for (_, var_decl) in &self.ty_constructors {
            for ty in var_decl {
                ty.find_used_types(&mut used);
            }
        }
        used
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LocalIdent {
    /// A MIR local along with an optional human-readable name
    Local(Local, Option<String>),

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

impl From<Local> for LocalIdent {
    fn from(l: Local) -> Self {
        Self::Local(l, None)
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
            LocalIdent::Local(l, n) => {
                if let Some(n) = n {
                    write!(f, "{}", n)?;
                }
                write!(f, "{:?}", l)
            }
            LocalIdent::Name(nm) => write!(f, "{}", nm),
        }
    }
}

use itertools::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QName {
    pub module: Vec<String>,
    // TODO: get rid of the vec here!
    pub name: Vec<String>,
}

impl QName {
    pub fn name(&self) -> String {
        format!("{}", self.name.iter().format("_"))
    }

    pub fn make_constructor(&mut self, cons_name: String) {
        use heck::CamelCase;

        self.name[0] = self.name[0].to_camel_case();
        self.name.push(cons_name);
    }
}

impl From<&rustc_span::Symbol> for QName {
    fn from(nm: &rustc_span::Symbol) -> Self {
        QName { module: vec![], name: vec![nm.to_string().into()] }
    }
}

// impl Display for QName {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}", self.module.iter().chain(self.name.iter()).format("."))
//     }
// }

#[derive(Debug, Clone)]
pub enum FullBinOp {
    And,
    Or,
    Other(BinOp),
}

impl From<BinOp> for FullBinOp {
    fn from(op: BinOp) -> Self {
        FullBinOp::Other(op)
    }
}

#[derive(Debug, Clone)]
pub enum Exp {
    Current(Box<Exp>),
    Final(Box<Exp>),
    Let { pattern: Pattern, arg: Box<Exp>, body: Box<Exp> },
    Var(LocalIdent),
    QVar(QName),
    RecUp { record: Box<Exp>, label: String, val: Box<Exp> },
    Tuple(Vec<Exp>),
    Constructor { ctor: QName, args: Vec<Exp> },
    BorrowMut(Box<Exp>),
    Const(Constant),
    BinaryOp(FullBinOp, Box<Exp>, Box<Exp>),
    UnaryOp(UnOp, Box<Exp>),
    Call(Box<Exp>, Vec<Exp>),
    Verbatim(String),
    // Seq(Box<Exp>, Box<Exp>),
    Abs(LocalIdent, Box<Exp>),
    Match(Box<Exp>, Vec<(Pattern, Exp)>),

    // Predicates
    Impl(Box<Exp>, Box<Exp>),
    Forall(Vec<(LocalIdent, Type)>, Box<Exp>),
    Exists(Vec<(LocalIdent, Type)>, Box<Exp>),
}

impl Exp {
    pub fn conj(l: Exp, r: Exp) -> Self {
        Exp::BinaryOp(FullBinOp::And, box l, box r)
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
    BitOr,
    BitXor,
    BitAnd,
    Shift,
    AddSub,
    Mul,
    PrefixOp,
    Term,
    Call,
}

impl Exp {
    fn precedence(&self) -> Precedence {
        use FullBinOp::Other;
        use Precedence::*;

        match self {
            Exp::Current(_) => PrefixOp,
            Exp::Final(_) => PrefixOp,
            Exp::Let { .. } => Let,
            Exp::Abs(_, _) => Let,
            Exp::Var(_) => Closed,
            Exp::QVar(_) => Closed,
            Exp::RecUp { .. } => Term,
            Exp::Tuple(_) => Closed,
            Exp::Constructor { .. } => Term,
            // Exp::Seq(_, _) => { Term }
            Exp::Match(_, _) => Term,
            Exp::BorrowMut(_) => Term,
            Exp::Const(_) => Closed,
            Exp::UnaryOp(UnOp::Neg, _) => PrefixOp,
            Exp::UnaryOp(UnOp::Not, _) => Call,
            Exp::BinaryOp(FullBinOp::And, _, _) => And,
            Exp::BinaryOp(FullBinOp::Or, _, _) => Or,
            Exp::BinaryOp(Other(op), _, _) => match op {
                BinOp::Add => AddSub,
                BinOp::Sub => AddSub,
                BinOp::Mul => Mul,
                BinOp::Div => Term,
                BinOp::Rem => Mul,
                BinOp::BitXor => BitXor,
                BinOp::BitAnd => BitAnd,
                BinOp::BitOr => BitOr,
                BinOp::Shl => Shift,
                BinOp::Shr => Shift,
                BinOp::Eq => Compare,
                BinOp::Lt => Compare,
                BinOp::Le => Compare,
                BinOp::Ne => Compare,
                BinOp::Ge => Compare,
                BinOp::Gt => Compare,
                BinOp::Offset => panic!("unsupported operator"),
            },
            Exp::Call(_, _) => Call,
            Exp::Verbatim(_) => Any,
            Exp::Impl(_, _) => Impl,
            Exp::Forall(_, _) => Any,
            Exp::Exists(_, _) => Any,
        }
    }

    pub fn fvs(&self) -> HashSet<LocalIdent> {
        match self {
            Exp::Current(e) => e.fvs(),
            Exp::Final(e) => e.fvs(),
            Exp::Let { pattern, arg, body } => {
                let bound = pattern.binders();

                &(&body.fvs() - &bound) | &arg.fvs()
            }
            Exp::Var(v) => {
                let mut fvs = HashSet::new();
                fvs.insert(v.clone());
                fvs
            }
            // Exp::QVar(_) => {}
            // Exp::RecUp { record, label, val } => {}
            // Exp::Tuple(_) => {}
            // Exp::Constructor { ctor, args } => {}
            // Exp::BorrowMut(_) => {}
            Exp::Const(_) => HashSet::new(),
            Exp::BinaryOp(_, l, r) => &l.fvs() | &r.fvs(),
            // Exp::Call(_, _) => {}
            Exp::Verbatim(_) => HashSet::new(),
            _ => unimplemented!(),
        }
    }

    pub fn subst(&mut self, mut subst: HashMap<LocalIdent, Exp>) {
        match self {
            Exp::Current(e) => e.subst(subst),
            Exp::Final(e) => e.subst(subst),
            Exp::Let { pattern, arg, body } => {
                arg.subst(subst.clone());
                let mut bound = pattern.binders();
                bound.drain().for_each(|k| {
                    subst.remove(&k);
                });

                body.subst(subst);
            }
            Exp::Var(v) => {
                if let Some(e) = subst.get(v) {
                    *self = e.clone()
                }
            }
            Exp::RecUp { record, val, .. } => {
                record.subst(subst.clone());
                val.subst(subst);
            }
            Exp::Tuple(tuple) => {
                for t in tuple {
                    t.subst(subst.clone());
                }
            }
            Exp::Constructor { args, .. } => {
                for a in args {
                    a.subst(subst.clone());
                }
            }
            Exp::Abs(ident, body) => {
                subst.remove(ident);
                body.subst(subst);
            }
            Exp::Match(box scrut, brs) => {
                scrut.subst(subst.clone());

                for (pat, br) in brs {
                    let mut s = subst.clone();
                    pat.binders().drain().for_each(|b| {
                        s.remove(&b);
                    });
                    br.subst(s);
                }
            }
            Exp::BorrowMut(e) => e.subst(subst),
            Exp::UnaryOp(_, o) => {
                o.subst(subst);
            }
            Exp::BinaryOp(_, l, r) => {
                l.subst(subst.clone());
                r.subst(subst)
            }
            Exp::Impl(hyp, exp) => {
                hyp.subst(subst.clone());
                exp.subst(subst)
            }
            Exp::Forall(binders, exp) => {
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });
                exp.subst(subst);
            }
            Exp::Exists(binders, exp) => {
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });
                exp.subst(subst);
            }
            Exp::Call(_, a) => {
                for arg in a {
                    arg.subst(subst.clone());
                }
            }
            Exp::QVar(_) => {}
            Exp::Const(_) => {}
            Exp::Verbatim(_) => {}
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
pub enum Constant {
    Int(i128),
    Uint(u128),
    // Float(f64),
    Other(String),
}
impl Constant {
    pub fn from_mir_constant<'tcx>(tcx: TyCtxt<'tcx>, c: &mir::Constant<'tcx>) -> Self {
        let mut fmt = String::new();
        let cx = FmtPrinter::new(tcx, &mut fmt, Namespace::ValueNS);
        cx.pretty_print_const(c.literal, false).unwrap();

        Constant::Other(fmt)
    }

    pub fn const_true() -> Self {
        Constant::Other("True".to_owned())
    }
    pub fn const_false() -> Self {
        Constant::Other("False".to_owned())
    }
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard,
    VarP(LocalIdent),
    TupleP(Vec<Pattern>),
    ConsP(QName, Vec<Pattern>),
    LitP(Constant),
    // RecP(String, String),
}

impl Pattern {
    pub fn binders(&self) -> HashSet<LocalIdent> {
        match self {
            Pattern::Wildcard => HashSet::new(),
            Pattern::VarP(s) => {
                let mut b = HashSet::new();
                b.insert(s.clone());
                b
            }
            Pattern::TupleP(pats) => pats.iter().map(|p| p.binders()).fold(HashSet::new(), |mut set, x| {
                set.extend(x);
                set
            }),
            Pattern::ConsP(_, args) => args.iter().map(|p| p.binders()).fold(HashSet::new(), |mut set, x| {
                set.extend(x);
                set
            }),
            Pattern::LitP(_) => HashSet::new(),
        }
    }
}
