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
    LogicDecl(Logic),
    // TyDecl(TyDecl),
    // PredDecl(Predicate),
}

#[derive(Debug, Default)]
pub struct Contract {
    pub requires: Vec<Exp>,
    pub ensures: Vec<Exp>,
    pub variant: Option<Exp>,
}

impl Contract {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn subst(&mut self, subst: &HashMap<LocalIdent, Exp>) {
        for req in self.requires.iter_mut() {
            req.subst(subst);
        }
        for ens in self.ensures.iter_mut() {
            ens.subst(subst);
        }
        if let Some(variant) = &mut self.variant {
            variant.subst(subst);
        }
    }
}
#[derive(Debug)]
pub struct Logic {
    pub name: QName,
    pub retty: Type,
    pub args: Vec<(LocalIdent, Type)>,
    pub body: Exp,
    pub contract: Contract,
}

#[derive(Debug)]
pub struct Function {
    pub name: QName,
    pub retty: Type,
    pub args: Vec<(LocalIdent, Type)>,
    pub vars: Vec<(LocalIdent, Type)>,
    pub blocks: BTreeMap<BlockId, Block>,
    pub contract: Contract,
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
    Assert(Exp),
}

#[derive(Debug, Clone)]
pub enum Type {
    Bool,
    Char,
    Integer,
    Int(rustc_middle::ty::IntTy),
    Uint(rustc_middle::ty::UintTy),
    Float(rustc_middle::ty::FloatTy),
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
        !matches!(
            self,
            Bool | Char | Integer | Int(_) | Uint(_) | TVar(_) | Tuple(_) | TConstructor(_)
        )
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
}

impl From<&rustc_span::Symbol> for QName {
    fn from(nm: &rustc_span::Symbol) -> Self {
        QName { module: vec![], name: vec![nm.to_string()] }
    }
}

impl From<&str> for QName {
    fn from(nm: &str) -> Self {
        QName { module: vec![], name: vec![nm.to_string()] }
    }
}

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
    RecField { record: Box<Exp>, label: String },
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
    Absurd,
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
            Exp::RecField { .. } => Any,
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
            Exp::Absurd => Closed,
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
            Exp::QVar(_) => HashSet::new(),
            // Exp::RecUp { record, label, val } => {}
            // Exp::Tuple(_) => {}
            Exp::Constructor { ctor: _, args } => {
                args.iter().fold(HashSet::new(), |acc, v| &acc | &v.fvs())
            }
            Exp::Const(_) => HashSet::new(),
            Exp::BinaryOp(_, l, r) => &l.fvs() | &r.fvs(),
            Exp::Call(f, args) => args.iter().fold(f.fvs(), |acc, a| &acc | &a.fvs()),
            Exp::Impl(h, c) => &h.fvs() | &c.fvs(),
            Exp::Forall(bnds, exp) => bnds.iter().fold(exp.fvs(), |mut acc, (l, _)| {
                acc.remove(l);
                acc
            }),
            Exp::BorrowMut(e) => e.fvs(),
            Exp::Verbatim(_) => HashSet::new(),
            _ => unimplemented!(),
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
                bound.drain().for_each(|k| {
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
                    pat.binders().drain().for_each(|b| {
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
pub enum Constant {
    Int(i128, Option<rustc_middle::ty::IntTy>),
    Uint(u128,  Option<rustc_middle::ty::UintTy>),
    // Float(f64),
    Other(String),
}
impl Constant {
    pub fn from_mir_constant<'tcx>(tcx: TyCtxt<'tcx>, c: &mir::Constant<'tcx>) -> Self {
        use rustc_middle::ty::TyKind::{Int, Uint};
        use rustc_middle::ty::{IntTy::*, UintTy::*};
        use rustc_target::abi::Size;

        match c.literal.ty.kind() {
            Int(I8) => { Constant::Int(c.literal.val.try_to_bits(Size::from_bytes(1)).unwrap() as i128, Some(I8)) }
            Int(I16) => { Constant::Int(c.literal.val.try_to_bits(Size::from_bytes(2)).unwrap() as i128, Some(I16)) }
            Int(I32) => { Constant::Int(c.literal.val.try_to_bits(Size::from_bytes(4)).unwrap() as i128, Some(I32)) }
            Int(I64) => { Constant::Int(c.literal.val.try_to_bits(Size::from_bytes(8)).unwrap() as i128, Some(I64)) }
            Int(I128) => { Constant::Int(c.literal.val.try_to_bits(Size::from_bytes(16)).unwrap() as i128, Some(I128)) }

            Uint(U8) => { Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(1)).unwrap(), Some(U8)) }
            Uint(U16) => { Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(2)).unwrap(), Some(U16)) }
            Uint(U32) => { Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(4)).unwrap(), Some(U32)) }
            Uint(U64) => { Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(8)).unwrap(), Some(U64)) }
            Uint(U128) => { Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(16)).unwrap(), Some(U128)) }
            Uint(Usize) => { Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(8)).unwrap(), Some(Usize)) }
            _ => {
                let mut fmt = String::new();
                let cx = FmtPrinter::new(tcx, &mut fmt, Namespace::ValueNS);
                cx.pretty_print_const(c.literal, false).unwrap();

                Constant::Other(fmt)
            }

        }
    }

    pub fn const_true() -> Self {
        Constant::Other("true".to_owned())
    }
    pub fn const_false() -> Self {
        Constant::Other("false".to_owned())
    }
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard,
    VarP(LocalIdent),
    TupleP(Vec<Pattern>),
    ConsP(QName, Vec<Pattern>),
    // RecP(String, String),
}

impl Pattern {
    pub fn mk_true() -> Self {
        Self::ConsP(QName { module: vec![], name: vec!["True".into()] }, vec![])
    }

    pub fn mk_false() -> Self {
        Self::ConsP(QName { module: vec![], name: vec!["False".into()] }, vec![])
    }

    pub fn binders(&self) -> HashSet<LocalIdent> {
        match self {
            Pattern::Wildcard => HashSet::new(),
            Pattern::VarP(s) => {
                let mut b = HashSet::new();
                b.insert(s.clone());
                b
            }
            Pattern::TupleP(pats) => {
                pats.iter().map(|p| p.binders()).fold(HashSet::new(), |mut set, x| {
                    set.extend(x);
                    set
                })
            }
            Pattern::ConsP(_, args) => {
                args.iter().map(|p| p.binders()).fold(HashSet::new(), |mut set, x| {
                    set.extend(x);
                    set
                })
            }
        }
    }
}
