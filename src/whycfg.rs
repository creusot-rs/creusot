use std::fmt::Display;

use rustc_middle::mir::Local;

#[derive(Debug)]
pub enum MlCfgStatement {
    Assign { lhs: Local, rhs: MlCfgExp },
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
    RecField { rec: Box<MlCfgExp>, field: String },
}

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
    RecP(String, String),
}

impl Display for MlCfgPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MlCfgPattern::Wildcard => { write!(f, "_")?; }
            MlCfgPattern::VarP(v) => { write!(f, "{}", v)?; }
            MlCfgPattern::TupleP(vs) => { write!(f, "({})", vs.iter().format(", "))?; }
            MlCfgPattern::ConsP(c, pats) => { write!(f, "{}({})", c, pats.iter().format(", "))?; }
            MlCfgPattern::RecP(l, n) => { write!(f, "{{ {} = {} }}", l, n)?; }
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
                write!(f, "{}({})", ctor, args.iter().format(", "))?;
            }
            MlCfgExp::BorrowMut(exp) => {
                write!(f, "borrow_mut {}", parens!(exp))?;
            }
            MlCfgExp::RecField{rec, field} => {
                write!(f, "{}.{}", parens!(rec), field)?;
            }
        }
        Ok(())
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
