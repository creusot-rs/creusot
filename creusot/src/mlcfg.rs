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
              use int.Int \n\
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
    Invariant(Exp),
    Freeze(LocalIdent),
}

#[derive(Debug)]
pub enum Type {
    Bool,
    Char,
    Int(rustc_ast::ast::IntTy),
    Uint(rustc_ast::ast::UintTy),
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
    BinaryOp(BinOp, Box<Exp>, Box<Exp>),
    Call(Constant, Vec<Exp>),
    Verbatim(String),
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
            Exp::Call(f, a) => {}
            Exp::QVar(_) => {}
            Exp::Const(_) => {}
            Exp::Verbatim(_) => {}
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

impl Exp {
    fn complex(&self) -> bool {
        use Exp::*;
        !matches!(self, Var(_) | Tuple(_) | Constructor{..} | Const(_))
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

macro_rules! parens {
    ($i:ident) => {
        if $i.complex() {
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
            write!(f, "({}_o : {})", nm, ty)?;
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
            writeln!(f, "  {} <- {}_o;", arg, arg)?;
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
                write!(f, "let {} = {} in {}", pattern, parens!(arg), parens!(body))?;
            }
            Exp::Var(v) => {
                write!(f, "{}", v)?;
            }
            Exp::QVar(v) => {
                write!(f, "{}", v)?;
            }
            Exp::RecUp { record, label, val } => {
                write!(f, "{{ {} with {} = {} }}", parens!(record), label, parens!(val))?;
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
                write!(f, "borrow_mut {}", parens!(exp))?;
            }
            // Exp::RecField{rec, field} => {
            //     write!(f, "{}.{}", parens!(rec), field)?;
            // }
            Exp::Const(c) => {
                write!(f, "{}", c)?;
            }
            Exp::BinaryOp(BinOp::Div, l, r) => {
                write!(f, "div {} {}", parens!(l), parens!(r))?;
            }
            Exp::BinaryOp(op, l, r) => {
                write!(f, "{} {} {}", parens!(l), bin_op_to_string(op), parens!(r))?;
            }
            Exp::Call(fun, args) => {
                write!(f, "{} {}", fun, args.iter().map(|a| parens!(a)).format(" "))?;
            }
            Exp::Verbatim(verb) => {
                write!(f, "{}", verb)?;
            }
        }
        Ok(())
    }
}

fn bin_op_to_string(op: &BinOp) -> &str {
    use rustc_middle::mir::BinOp::*;
    match op {
        Add => "+",
        Sub => "-",
        Mul => "*",
        Eq => "=",
        Ne => "<>",
        Gt => ">",
        Ge => ">=",
        Lt => "<",
        Le => "<=",
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
            Statement::Invariant(e) => {
                write!(f, "invariant {{ {} }}", e)?;
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
            Int(_) => {
                write!(f, "int")?;
            } // TODO machine ints
            Uint(_) => {
                write!(f, "int")?;
            } // TODO uints
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
