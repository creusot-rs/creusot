use std::fmt::Display;

// Imports related to MLCfg Constatns
use rustc_middle::{
    mir::{BinOp, self},
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
    pub args: Vec<(Local, Type)>,
    pub vars: Vec<(Local, Type)>,
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
    Assign { lhs: Local, rhs: Exp },
    Invariant(Exp),
    Freeze(Local),
}

#[derive(Debug)]
pub enum Type {
    Bool,
    Char,
    Int(rustc_ast::ast::IntTy),
    Uint(rustc_ast::ast::UintTy),
    MutableBorrow(Box<Type>),
    TVar(String),
    TConstructor(String),
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

#[derive(Debug, Clone)]
pub enum Exp {
    Current(Box<Exp>),
    Final(Box<Exp>),
    Local(Local),
    Let { pattern: Pattern, arg: Box<Exp>, body: Box<Exp> },
    Var(String),
    RecUp { record: Box<Exp>, label: String, val: Box<Exp> },
    Tuple(Vec<Exp>),
    Constructor { ctor: String, args: Vec<Exp> },
    BorrowMut(Box<Exp>),
    // RecField { rec: Box<Exp>, field: String },
    Const(Constant),
    BinaryOp(BinOp, Box<Exp>, Box<Exp>),
    Call(Box<Exp>, Vec<Exp>),
    Verbatim(String),
}

#[derive(Debug, Clone)]
pub struct Constant(String, ConstantType);

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

// TODO: Add Constant Types
type ConstantType = ();
// enum ConstantType { Bool }

impl Exp {
    fn complex(&self) -> bool {
        use Exp::*;
        !matches!(self, Local(_) | Var(_) | Tuple(_) | Constructor{..})
    }
}
#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard,
    VarP(String),
    TupleP(Vec<Pattern>),
    ConsP(String, Vec<Pattern>),
    LitP(Constant),
    // RecP(String, String),
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
            write!(f, "({:?}_o : {})", nm, ty)?;
        }

        writeln!(f, " : {}", self.retty)?;

        for req in &self.preconds {
            writeln!(f,"requires {{ {} }}", req)?;
        }
        for req in &self.postconds {
            writeln!(f,"ensures {{ {} }}", req)?;
        }

        writeln!(f, "=")?;
        // Forward declare all arguments
        writeln!(f, "var _0 : {};", self.retty)?;

        for (var, ty) in self.args.iter() {
            writeln!(f, "var {:?} : {};", var, ty)?;
        }

        // Forward declare all variables
        for (var, ty) in self.vars.iter() {
            writeln!(f, "var {:?} : {};", var, ty)?;
        }
        writeln!(f, "{{")?;

        for (arg, _) in self.args.iter() {
            writeln!(f, "  {:?} <- {:?}_o;", arg, arg)?;
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
            Exp::Local(l) => {
                write!(f, "{:?}", l)?;
            }
            Exp::Let { pattern, arg, body } => {
                write!(f, "let {} = {} in {}", pattern, parens!(arg), parens!(body))?;
            }
            Exp::Var(v) => {
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
            Exp::BinaryOp(op, l, r) => {
                write!(f, "{} {} {}", l, bin_op_to_string(op), r)?;
            }
            Exp::Call(fun, args) => {
                write!(f, "{} {}", fun, args.iter().map(|a| parens!(a)).format(" "))?;
            }
            Exp::Verbatim(verb) => { write!(f, "{}", verb)?; }
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
        Div => "/",
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
                write!(f, "{:?} <- {}", lhs, rhs)?;
            }
            Statement::Freeze(loc) => {
                write!(f, "assume {{ ^ {:?} = * {:?} }}", loc, loc)?;
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
