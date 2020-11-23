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
    pub name: String,
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
pub struct MlTyDecl {
    pub ty_name: String,
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

impl LocalIdent {
    fn to_string(&self) -> String {
        format!("{}", self)
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

#[derive(Debug, Clone)]
pub struct QName {
    pub segments: Vec<String>,
}

impl QName {
    pub fn unqual_name(&self) -> &str {
        self.segments.last().unwrap()
    }
}

impl From<&rustc_span::Symbol> for QName {
    fn from(nm: &rustc_span::Symbol) -> Self {
        QName { segments: vec![nm.to_string().into()] }
    }
}

impl Display for QName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.segments.iter().format("."))
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
    Call(Constant, Vec<Exp>),
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

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Wildcard => {
                write!(f, "_")?;
            }
            Pattern::VarP(v) => {
                write!(f, "{}", v)?;
            }
            Pattern::TupleP(vs) => {
                write!(f, "({})", vs.iter().format(", "))?;
            }
            Pattern::ConsP(c, pats) => {
                if pats.is_empty() {
                    write!(f, "{}", c)?;
                } else {
                    write!(f, "{}({})", c, pats.iter().format(", "))?;
                }
            }
            Pattern::LitP(lit) => {
                write!(f, "{}", lit)?;
            }
        }
        Ok(())
    }
}

use itertools::*;

// FIXME: Doesn't take into account associativity when deciding when to put parens
macro_rules! parens {
    ($e:ident, $i:ident) => {
        if $i.precedence() < $e.precedence() {
            format!("({})", $i)
        } else {
            format!("{}", $i)
        }
    };
}

impl Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BB{}", self.0)
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "let cfg {} ", self.name)?;

        if self.args.is_empty() {
            write!(f, "()")?;
        }

        for (nm, ty) in &self.args {
            write!(f, "(o_{} : {})", nm, ty)?;
        }

        writeln!(f, " : {}", self.retty)?;

        for req in &self.preconds {
            writeln!(f, "requires {{ {} }}", req)?;
        }
        for req in &self.postconds {
            writeln!(f, "ensures {{ {} }}", req)?;
        }

        writeln!(f, "=")?;
        // Forward declare all arguments
        writeln!(f, "var _0 : {};", self.retty)?;

        for (var, ty) in self.args.iter() {
            writeln!(f, "var {} : {};", var, ty)?;
        }

        // Forward declare all variables
        for (var, ty) in self.vars.iter() {
            writeln!(f, "var {} : {};", var, ty)?;
        }
        writeln!(f, "{{")?;

        for (arg, _) in self.args.iter() {
            writeln!(f, "  {} <- o_{};", arg, arg)?;
        }

        writeln!(f, "  goto BB0;")?;
        writeln!(f, "}}")?;

        for block in &self.blocks {
            write!(f, "{}", block)?;
        }

        Ok(())
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{} {{", self.label)?;

        for stmt in &self.statements {
            writeln!(f, "  {};", stmt)?;
        }

        writeln!(f, "  {}", self.terminator)?;

        writeln!(f, "}}")?;

        Ok(())
    }
}

impl Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Terminator::*;
        match self {
            Goto(tgt) => {
                write!(f, "goto {}", tgt)?;
            }
            Absurd => {
                write!(f, "absurd")?;
            }
            Return => {
                write!(f, "_0")?;
            }
            Switch(discr, brs) => {
                writeln!(f, "switch ({})", discr)?;

                for (pat, tgt) in brs {
                    writeln!(f, "  | {} -> goto {}", pat, tgt)?;
                }
                writeln!(f, "  end")?;
            }
        }
        Ok(())
    }
}

impl Display for Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Exp::Current(e) => {
                write!(f, " * {}", e)?;
            }
            Exp::Final(e) => {
                write!(f, " ^ {}", e)?;
            }
            Exp::Let { pattern, arg, body } => {
                write!(f, "let {} = {} in {}", pattern, parens!(self, arg), parens!(self, body))?;
            }
            Exp::Var(v) => {
                write!(f, "{}", v)?;
            }
            // Exp::QVar(v) => {
            //     write!(f, "{}", v)?;
            // }
            Exp::RecUp { record, label, val } => {
                write!(f, "{{ {} with {} = {} }}", parens!(self, record), label, parens!(self, val))?;
            }
            Exp::Tuple(vs) => {
                write!(f, "({})", vs.iter().format(", "))?;
            }
            Exp::Constructor { ctor, args } => {
                if args.is_empty() {
                    write!(f, "{}", ctor)?;
                } else {
                    write!(f, "{}({})", ctor, args.iter().format(", "))?;
                }
            }
            Exp::BorrowMut(exp) => {
                write!(f, "borrow_mut {}", parens!(self, exp))?;
            }
            Exp::Const(c) => {
                write!(f, "{}", c)?;
            }
            Exp::BinaryOp(FullBinOp::Other(BinOp::Div), l, r) => {
                write!(f, "div {} {}", parens!(self, l), parens!(self, r))?;
            }
            Exp::BinaryOp(op, l, r) => {
                write!(f, "{} {} {}", parens!(self, l), bin_op_to_string(op), parens!(self, r))?;
            }
            Exp::Call(fun, args) => {
                write!(f, "{} {}", fun, args.iter().map(|a| parens!(self, a)).format(" "))?;
            }
            Exp::Verbatim(verb) => {
                write!(f, "{}", verb)?;
            }
            Exp::Forall(binders, exp) => {
                write!(f, "forall ")?;

                for (l, ty) in binders {
                    write!(f, "({} : {}) ", l, ty)?;
                }

                write!(f, ". {}", exp)?;
            }
            Exp::Exists(binders, exp) => {
                write!(f, "exists ")?;

                for (l, ty) in binders {
                    write!(f, "({} : {}) ", l, ty)?;
                }

                write!(f, ". {}", exp)?;
            }
            Exp::Impl(hyp, exp) => {
                write!(f, "{} -> {}", parens!(self, hyp), parens!(self, exp))?;
            }
        }
        Ok(())
    }
}

fn bin_op_to_string(op: &FullBinOp) -> &str {
    use FullBinOp::*;
    use rustc_middle::mir::BinOp::*;
    match op {
        And => "&&",
        Or => "||",
        Other(Add) => "+",
        Other(Sub) => "-",
        Other(Mul) => "*",
        Other(Eq )=> "=",
        Other(Ne )=> "<>",
        Other(Gt )=> ">",
        Other(Ge )=> ">=",
        Other(Lt )=> "<",
        Other(Le )=> "<=",
        _ => unimplemented!("unsupported bin op"),
    }
}

impl Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Assign { lhs, rhs } => {
                write!(f, "{} <- {}", lhs, rhs)?;
            }
            Statement::Freeze(loc) => {
                write!(f, "assume {{ ^ {} = * {} }}", loc, loc)?;
            }
            Statement::Invariant(nm, e) => {
                write!(f, "invariant {} {{ {} }}", nm, e)?;
            }
        }
        Ok(())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type::*;

        if self.complex() {
            write!(f, "(")?;
        }
        match self {
            Bool => {
                write!(f, "bool")?;
            }
            Char => {
                write!(f, "char")?;
            }
            Int(size) => {
                use rustc_ast::ast::IntTy::*;
                match size {
                    I8      => write!(f, "int8"),
                    I16     => write!(f, "int16"),
                    I32     => write!(f, "int32"),
                    I64     => write!(f, "int64"),
                    I128    => write!(f, "int128"),
                    Isize   => write!(f, "isize"),
                }?
            }
            Uint(size) => {
                use rustc_ast::ast::UintTy::*;
                match size {
                    U8      => write!(f, "uint8"),
                    U16     => write!(f, "uint16"),
                    U32     => write!(f, "uint32"),
                    U64     => write!(f, "uint64"),
                    U128    => write!(f, "uint128"),
                    Usize   => write!(f, "usize"),
                }?
            }
            Float(size) => {
                use rustc_ast::ast::FloatTy::*;
                match size {
                    F32 => write!(f, "single"),
                    F64 => write!(f, "double"),
                }?
            }
            MutableBorrow(t) => {
                write!(f, "borrowed {}", t)?;
            }
            TVar(v) => {
                write!(f, "{}", v)?;
            }
            TConstructor(ty) => {
                write!(f, "{}", ty)?;
            }
            TApp(tyf, args) => {
                write!(f, "{} {}", tyf, args.iter().format(" "))?;
            }
            Tuple(tys) => {
                write!(f, "({})", tys.iter().format(", "))?;
            }
        }
        if self.complex() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl Display for MlTyDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "type {} {} =", self.ty_name, self.ty_params.iter().format(" "))?;

        for (cons, args) in self.ty_constructors.iter() {
            if args.is_empty() {
                writeln!(f, "  | {}", cons)?;
            } else {
                writeln!(f, "  | {}({})", cons, args.iter().format(", "))?;
            }
        }

        Ok(())
    }
}
