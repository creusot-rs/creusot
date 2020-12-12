use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;

// Imports related to MLCfg Constatns
use rustc_middle::{
    mir::{self, BinOp},
    ty::{print::FmtPrinter, print::PrettyPrinter, TyCtxt},
};

use rustc_hir::def::Namespace;
use rustc_middle::mir::{BasicBlock, Local};

pub mod printer;

pub const PRELUDE: &str = "use Ref \n\
              use mach.int.Int \n\
              use mach.int.Int32\n\
              use mach.int.Int64\n\
              use mach.int.UInt32\n\
              use mach.int.UInt64\n\
              use string.Char\n\

              use floating_point.Single\n\
              use floating_point.Double\n\
              (** Generic Type for borrowed values *) \n\
              type borrowed 'a = \n\
                { current : 'a ; \n\
                  final : 'a; (* The \"future\" value when borrow will end *) \n\
                } \n\
              let function ( *_ ) x = x.current \n\
              let function ( ^_ ) x = x.final \n\
              val borrow_mut (a : 'a) : borrowed 'a \n\
                 ensures { *result = a }";

#[derive(Debug)]
pub struct Function {
    pub name: QName,
    pub retty: Type,
    pub args: Vec<(LocalIdent, Type)>,
    pub vars: Vec<(LocalIdent, Type)>,
    pub blocks: Vec<Block>,
    pub preconds: Vec<String>, // for now we blindly pass contracts down
    pub postconds: Vec<String>,
}

#[derive(Debug)]
pub struct Block {
    pub label: BlockId,
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug)]
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
    Switch(Exp, Vec<(Pattern, BlockId)>),
}

#[derive(Debug)]
pub enum Statement {
    Assign { lhs: LocalIdent, rhs: Exp },
    Invariant(String, Exp),
    Freeze(LocalIdent),
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
}

impl Type {
    fn complex(&self) -> bool {
        use Type::*;
        !matches!(self, Bool | Char | Int(_) | Uint(_) | TVar(_) | Tuple(_) | TConstructor(_))
    }
}

#[derive(Debug)]
pub struct TyDecl {
    pub ty_name: QName,
    pub ty_params: Vec<String>,
    pub ty_constructors: Vec<(String, Vec<Type>)>,
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

#[derive(Debug, Clone)]
pub struct QName {
    pub module: Vec<String>,
    pub name: Vec<String>,
}

impl QName {
    pub fn replace_name(&mut self, cons: String) {
        self.name = vec![cons];
    }
}

impl From<&rustc_span::Symbol> for QName {
    fn from(nm: &rustc_span::Symbol) -> Self {
        QName { module: vec![], name: vec![nm.to_string().into()] }
    }
}

impl Display for QName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.module.iter().chain(self.name.iter()).format("."))
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
    // QVar(QName),
    RecUp { record: Box<Exp>, label: String, val: Box<Exp> },
    Tuple(Vec<Exp>),
    Constructor { ctor: QName, args: Vec<Exp> },
    BorrowMut(Box<Exp>),
    Const(Constant),
    BinaryOp(FullBinOp, Box<Exp>, Box<Exp>),
    Call(QName, Vec<Exp>),
    Verbatim(String),

    // Predicates

    Impl(Box<Exp>, Box<Exp>),
    Forall(Vec<(LocalIdent, Type)>, Box<Exp>),
    Exists(Vec<(LocalIdent, Type)>, Box<Exp>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Any,
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
    FinCur,
    Term,
}

impl Exp {
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
            Exp::Constructor {args, .. } => {
                for a in args {
                    a.subst(subst.clone());
                }
            }
            Exp::BorrowMut(e) => { e.subst(subst) }
            Exp::BinaryOp(_, l, r) => { l.subst(subst.clone()); r.subst(subst)}
            Exp::Impl(hyp, exp) => { hyp.subst(subst.clone()); exp.subst(subst)}
            Exp::Forall(binders, exp) => {
                binders.iter().for_each(|k| { subst.remove(&k.0); });
                exp.subst(subst);
            }
            Exp::Exists(binders, exp) => {
                binders.iter().for_each(|k| { subst.remove(&k.0); });
                exp.subst(subst);
            }
            Exp::Call(_, a) => {
                for arg in a {
                    arg.subst(subst.clone());
                }
            }
            // Exp::QVar(_) => {}
            Exp::Const(_) => {}
            Exp::Verbatim(_) => {}
        }
    }

    fn precedence(&self) -> Precedence {
        use Precedence::*;
        use FullBinOp::Other;

        match self {
            Exp::Current(_) => { FinCur }
            Exp::Final(_) => { FinCur }
            Exp::Let { .. } => { Any }
            Exp::Var(_) => { Term }
            Exp::RecUp { .. } => { Term }
            Exp::Tuple(_) => { Term }
            Exp::Constructor { .. } => { Term }
            Exp::BorrowMut(_) => { Any }
            Exp::Const(_) => { Term }
            Exp::BinaryOp(FullBinOp::And, _, _) => { And }
            Exp::BinaryOp(FullBinOp::Or, _, _) => { Or }
            Exp::BinaryOp(Other(op), _, _) => {
                match op {
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
                    BinOp::Eq  => Compare,
                    BinOp::Lt  => Compare,
                    BinOp::Le  => Compare,
                    BinOp::Ne  => Compare,
                    BinOp::Ge  => Compare,
                    BinOp::Gt  => Compare,
                    BinOp::Offset => panic!("unsupported operator"),
                }
            }
            Exp::Call(_, _) => { Term }
            Exp::Verbatim(_) => { Any }
            Exp::Impl(_, _) => { Impl }
            Exp::Forall(_, _) => { Any }
            Exp::Exists(_, _) => { Any }
        }
    }
}

type ConstantType = ();

#[derive(Debug, Clone)]
pub struct Constant(pub String, pub ConstantType);

impl Constant {
    pub fn from_mir_constant<'tcx>(tcx: TyCtxt<'tcx>, c: &mir::Constant<'tcx>) -> Self {
        let mut fmt = String::new();
        let cx = FmtPrinter::new(tcx, &mut fmt, Namespace::ValueNS);
        cx.pretty_print_const(c.literal, false).unwrap();

        Constant(fmt, ())
    }

    pub fn const_true() -> Self {
        Constant("True".to_owned(), ())
    }
    pub fn const_false() -> Self {
        Constant("False".to_owned(), ())
    }
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard,
    VarP(LocalIdent),
    TupleP(Vec<Pattern>),
    ConsP(String, Vec<Pattern>),
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
            Pattern::LitP(_) => HashSet::new(),
        }
    }
}

