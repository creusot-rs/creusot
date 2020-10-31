use std::fmt::Display;

// Imports related to MLCfg Constatns
use rustc_middle::{mir::{BinOp, Constant}, ty::{print::PrettyPrinter, TyCtxt, print::FmtPrinter}};

use rustc_hir::def::Namespace;
use rustc_middle::mir::{BasicBlock, Local};

pub const PRELUDE : &str = "use Ref \n\
              use int.Int \n\
              (** Generic Type for borrowed values *) \n\
              type borrowed 'a = \n\
                {{ current : 'a ; \n\
                  final : 'a; (* The \"future\" value when borrow will end *) \n\
                }} \n\
              let function ( *_ ) x = x.current \n\
              let function ( ^_ ) x = x.final \n\
              val borrow_mut (a : 'a) : borrowed 'a \n\
                 ensures {{ *result = a }}";

#[derive(Debug)]
pub struct MlCfgFunction {
    pub name: String,
    pub args: Vec<(Local, MlCfgType)>,
    pub vars: Vec<(Local, MlCfgType)>,
    pub blocks: Vec<MlCfgBlock>,
}

#[derive(Debug)]
pub struct MlCfgBlock {
    pub label: Block,
    pub statements: Vec<MlCfgStatement>,
    pub terminator: MlCfgTerminator,
}

#[derive(Debug)]
pub struct Block(usize);

impl From<&BasicBlock> for Block {
    fn from(b: &BasicBlock) -> Self {
        Block((*b).into())
    }
}
impl From<BasicBlock> for Block {
    fn from(b: BasicBlock) -> Self {
        Block(b.into())
    }
}

#[derive(Debug)]
pub enum MlCfgTerminator {
    Goto(Block),
    Absurd,
    Return,
    Switch(MlCfgExp, Vec<(MlCfgPattern, Block)>),
}

#[derive(Debug)]
pub enum MlCfgStatement {
    Assign { lhs: Local, rhs: MlCfgExp },
}

#[derive(Debug)]
pub enum MlCfgType {
    Bool,
    Char,
    Int(rustc_ast::ast::IntTy),
    Uint(rustc_ast::ast::UintTy),
    MutableBorrow(Box<MlCfgType>),
    TVar(String),
    TConstructor(String),
    TApp(Box<MlCfgType>, Vec<MlCfgType>),
    Tuple(Vec<MlCfgType>),
}

impl MlCfgType {
    fn complex(&self) -> bool {
        use MlCfgType::*;
        match self {
            Bool | Char | Int(_) | Uint(_) | TVar(_) | Tuple(_) | TConstructor(_) => false,
            _ => true,
        }
    }
}

#[derive(Debug)]
pub struct MlTyDecl {
    pub ty_name: String,
    pub ty_params: Vec<String>,
    pub ty_constructors: Vec<(String, Vec<MlCfgType>)>,
}

#[derive(Debug)]
pub enum MlCfgExp {
    Current(Box<MlCfgExp>),
    Final(Box<MlCfgExp>),
    Local(Local),
    Let { pattern: MlCfgPattern, arg: Box<MlCfgExp>, body: Box<MlCfgExp> },
    Var(String),
    RecUp { record: Box<MlCfgExp>, label: String, val: Box<MlCfgExp> },
    Tuple(Vec<MlCfgExp>),
    Constructor { ctor: String, args: Vec<MlCfgExp> },
    BorrowMut(Box<MlCfgExp>),
    // RecField { rec: Box<MlCfgExp>, field: String },
    Const(MlCfgConstant),
    BinaryOp(BinOp, Box<MlCfgExp>, Box<MlCfgExp>),
    Call(Box<MlCfgExp>, Vec<MlCfgExp>),
}

impl MlCfgExp {
    fn complex_exp(&self) -> bool {
        use MlCfgExp::*;
        match self {
            | Local(_) | Var(_) | Tuple(_) | Const(_) => false,
            // | RecField { .. } => false,
            _ => true,
        }
    }
}

#[derive(Debug)]
pub struct MlCfgConstant(String, ConstantType);

impl MlCfgConstant {
    pub fn from_mir_constant<'tcx> (tcx: TyCtxt<'tcx>, c: &Constant<'tcx>) -> Self {
        let mut fmt = String::new();
        let cx = FmtPrinter::new(tcx, &mut fmt, Namespace::ValueNS);
        cx.pretty_print_const(c.literal, false).unwrap();

        MlCfgConstant(fmt, ())
    }
}

// TODO: Add Constant Types
type ConstantType = ();
// enum ConstantType { Bool }

impl MlCfgExp {
    fn complex(&self) -> bool {
        use MlCfgExp::*;
        match self {
            Local(_) | Var(_) | Tuple(_) | Constructor{..} => false,
            _ => true,
        }
    }
}
#[derive(Clone, Debug)]
pub enum MlCfgPattern {
    Wildcard,
    VarP(String),
    TupleP(Vec<MlCfgPattern>),
    ConsP(String, Vec<MlCfgPattern>),
    // RecP(String, String),
}

impl Display for MlCfgPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MlCfgPattern::Wildcard => { write!(f, "_")?; }
            MlCfgPattern::VarP(v) => { write!(f, "{}", v)?; }
            MlCfgPattern::TupleP(vs) => { write!(f, "({})", vs.iter().format(", "))?; }
            MlCfgPattern::ConsP(c, pats) => {
                if pats.is_empty() {
                    write!(f, "{}", c)?;
                } else {
                    write!(f, "{}({})", c, pats.iter().format(", "))?;
                }
            }
            // MlCfgPattern::RecP(l, n) => { write!(f, "{{ {} = {} }}", l, n)?; }
        }
        Ok(())
    }
}

use itertools::*;

macro_rules! parens {
    ($i:ident) => {
        if $i.complex() { format!("({})", $i) } else { format!("{}", $i)}
    };
}

macro_rules! parens_exp {
    ($i:ident) => {
        if $i.complex_exp() { format!("({})", $i) } else { format!("{}", $i)}
    };
}


impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BB{}", self.0)
    }
}
impl Display for MlCfgFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "let cfg {} ", self.name)?;
        for (nm, ty) in &self.args {
            write!(f, "({:?} : {})", nm, ty)?;
        }

        writeln!(f, " =")?;

        // Forward declare all arguments
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

impl Display for MlCfgBlock {
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

impl Display for MlCfgTerminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use MlCfgTerminator::*;
        match self {
            Goto(tgt) => {
                write!(f, "goto {}", tgt)?;
            }
            Absurd => {
                write!(f, "absurd")?;
            }
            Return => {
                write!(f, "return _0")?;
            }
            Switch(discr, brs) => {
                writeln!(f,"switch {} {{", discr)?;

                for (pat, tgt) in brs {
                    writeln!(f, "  | {} -> goto {}", pat, tgt)?;
                }

                writeln!(f, "}}")?;
            }
        }
        Ok(())
    }
}


impl Display for MlCfgExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MlCfgExp::Current(e) => {
                write!(f, " * {}", e)?;
            }
            MlCfgExp::Final(e) => {
                write!(f, " ^ {}", e)?;
            }
            MlCfgExp::Local(l) => {
                write!(f, "{:?}", l)?;
            }
            MlCfgExp::Let { pattern, arg, body } => {
                write!(f, "let {} = {} in {}", pattern, parens!(arg) , parens!(body))?;
            }
            MlCfgExp::Var(v) => { write!(f, "{}", v)?; }
            MlCfgExp::RecUp { record, label, val } => {
                write!(f, "{{ {} with {} = {} }}", parens!(record), label, parens!(val))?;
            }
            MlCfgExp::Tuple(vs) => {
                write!(f, "({})", vs.iter().format(", "))?;
            }
            MlCfgExp::Constructor { ctor, args } => {
                if args.is_empty() {
                    write!(f, "{}", ctor)?;
                } else {
                    write!(f, "{}({})", ctor, args.iter().format(", "))?;
                }
            }
            MlCfgExp::BorrowMut(exp) => {
                write!(f, "borrow_mut {}", parens!(exp))?;
            }
            // MlCfgExp::RecField{rec, field} => {
            //     write!(f, "{}.{}", parens!(rec), field)?;
            // }
            MlCfgExp::Const(c) => { write!(f, "{}", c)?; }
            MlCfgExp::BinaryOp(op, l, r) => {
                write!(f, "{} {} {}", l, bin_op_to_string(op), r)?;
            }
            MlCfgExp::Call(fun, args) => {
                write!(f, "{} {}", fun, args.iter().map(|a| parens_exp!(a)).format(" "))?;
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

impl Display for MlCfgConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for MlCfgStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MlCfgStatement::Assign { lhs, rhs } => {
                write!(f, "{:?} <- {}", lhs, rhs)?;
            }
        }
        Ok(())
    }
}

impl Display for MlCfgType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use MlCfgType::*;

        if self.complex() { write!(f, "(")?; }
        match self {
            Bool => { write!(f, "bool")?; }
            Char => { write!(f, "char")?; }
            Int(_) => { write!(f, "int")?; } // TODO machine ints
            Uint(_) => { write!(f, "uint")?; } // TODO uints
            MutableBorrow(t) => { write!(f, "borrowed {}", t)?; }
            TVar(v) => { write!(f, "{}", v)?; }
            TConstructor(ty) => { write!(f, "{}", ty)?; }
            TApp(tyf, args) => { write!(f, "{} {}", tyf, args.iter().format(" "))?; }
            Tuple(tys) => { write!(f, "({})", tys.iter().format(", "))?; }
        }
        if self.complex() { write!(f, ")")?; }
        Ok(())
    }
}


impl Display for MlTyDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "type {} {} =\n", self.ty_name, self.ty_params.iter().format(" "))?;

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
