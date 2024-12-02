#[cfg(feature = "serde")]
use serde::Deserialize;
use serde_json::Value as Json;
use std::fmt::{Debug, Formatter};

#[cfg_attr(feature = "serde", derive(Deserialize))]
#[cfg_attr(feature = "serde", serde(untagged))]
pub enum Loc {
    Span(Why3Span),
    Other(Json),
}

#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Deserialize, Debug))]
#[cfg_attr(feature = "serde", serde(rename_all = "kebab-case"))]
pub struct Why3Span {
    pub file_name: String,
    pub start_line: u32,
    pub start_char: u32,
    pub end_line: u32,
    pub end_char: u32,
}

impl Debug for Loc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Loc::Span(Why3Span { file_name, start_line, start_char, end_line, end_char }) => {
                write!(f, "[#\"{file_name}\" {start_line} {start_char} {end_line} {end_char}]")
            }
            _ => write!(f, "[#???]"),
        }
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
#[cfg_attr(feature = "serde", serde(untagged))]
pub enum Fallible<T> {
    Ok(T),
    Err(Json),
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
#[cfg_attr(feature = "serde", serde(untagged))]
pub enum Model {
    Model { answer: String, model: Vec<Fallible<Model2>> },
    Unknown(Json),
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct Model2 {
    pub filename: String,
    pub model: Vec<Fallible<Model3>>,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct Model3 {
    pub is_vc_line: bool,
    pub line: String,
    pub model_elements: Vec<Fallible<ModelElem>>,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct LSymbol {
    pub name: String,
    pub attrs: Vec<String>,
    pub loc: Loc,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct ModelElem {
    pub attrs: Vec<String>,
    pub kind: String,
    pub location: Loc,
    pub lsymbol: LSymbol,
    pub value: Value,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct Value {
    pub value_concrete_term: ConcreteTerm,
    pub value_term: Term,
    pub value_type: Type,
}

#[cfg_attr(feature = "serde", derive(Deserialize))]
pub enum Type {
    #[cfg_attr(feature = "serde", serde(rename = "Tyvar"))]
    Var(String),
    #[cfg_attr(feature = "serde", serde(rename = "Tyapp"))]
    App { ty_symbol: String, ty_args: Vec<Type> },
    #[cfg_attr(feature = "serde", serde(untagged))]
    Unknown(Json),
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Var(v) => write!(f, "*{v}"),
            Type::App { ty_symbol, ty_args } => {
                write!(f, "{ty_symbol}")?;
                if !ty_args.is_empty() {
                    f.debug_list().entries(ty_args).finish()?;
                }
                Ok(())
            }
            Type::Unknown(json) => write!(f, "{json}"),
        }
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct VSymbol {
    pub vs_name: String,
    pub vs_type: Type,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub enum TBool {
    #[cfg_attr(feature = "serde", serde(rename = "Ttrue"))]
    True,
    #[cfg_attr(feature = "serde", serde(rename = "Tfalse"))]
    False,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub enum Term {
    #[cfg_attr(feature = "serde", serde(rename = "Tvar"))]
    Var(VSymbol),
    #[cfg_attr(feature = "serde", serde(rename = "Tconst"))]
    Const {
        #[cfg_attr(feature = "serde", serde(rename = "const_type"))]
        ty: String,
        #[cfg_attr(feature = "serde", serde(rename = "const_value"))]
        val: String,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Tapp"))]
    App {
        #[cfg_attr(feature = "serde", serde(rename = "app_ls"))]
        ls: String,
        #[cfg_attr(feature = "serde", serde(rename = "app_args"))]
        args: Vec<Term>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Tif"))]
    If {
        #[cfg_attr(feature = "serde", serde(rename = "if"))]
        ift: Box<Term>,
        then: Box<Term>,
        #[cfg_attr(feature = "serde", serde(rename = "else"))]
        elset: Box<Term>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Teps"))]
    Eps {
        #[cfg_attr(feature = "serde", serde(rename = "eps_vs"))]
        vs: VSymbol,
        #[cfg_attr(feature = "serde", serde(rename = "eps_t"))]
        t: Box<Term>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Tfun"))]
    Fun {
        #[cfg_attr(feature = "serde", serde(rename = "fun_args"))]
        args: Vec<VSymbol>,
        #[cfg_attr(feature = "serde", serde(rename = "fun_body"))]
        body: Box<Term>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Tquant"))]
    Quant {
        quant: String,
        #[cfg_attr(feature = "serde", serde(rename = "quant_vs"))]
        vs: Vec<VSymbol>,
        #[cfg_attr(feature = "serde", serde(rename = "quant_t"))]
        t: Box<Term>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Tbinop"))]
    Binop {
        binop: String,
        #[cfg_attr(feature = "serde", serde(rename = "binop_t1"))]
        t1: Box<Term>,
        #[cfg_attr(feature = "serde", serde(rename = "binop_t2"))]
        t2: Box<Term>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Tnot"))]
    Not(Box<Term>),
    #[cfg_attr(feature = "serde", serde(rename = "Tlet"))]
    Let(String),
    #[cfg_attr(feature = "serde", serde(rename = "Tcase"))]
    Case(String),
    #[cfg_attr(feature = "serde", serde(untagged))]
    Bool(TBool),
    #[cfg_attr(feature = "serde", serde(untagged))]
    Unknown(Json),
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct BitVector {
    pub bv_value_as_decimal: String,
    pub bv_length: u32,
    pub bv_verbatim: String,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct Real {
    pub real_value: String,
    pub real_verbatim: String,
}

#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct Integer {
    pub int_value: String,
    pub int_verbatim: String,
}

impl Integer {
    fn try_to_u64(&self) -> Option<u64> {
        if self.int_value != self.int_verbatim {
            None
        } else {
            self.int_value.parse().ok()
        }
    }
}

impl Debug for Integer {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.try_to_u64() {
            Some(n) => write!(f, "{n}"),
            None => f
                .debug_struct("Integer")
                .field("value", &self.int_value)
                .field("verbatim", &self.int_verbatim)
                .finish(),
        }
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub enum Float {
    Infinity,
    #[cfg_attr(feature = "serde", serde(rename = "Plus_zero"))]
    PlusZero,
    #[cfg_attr(feature = "serde", serde(rename = "Minus_zero"))]
    MinusZero,
    #[cfg_attr(feature = "serde", serde(rename = "Float_value"))]
    Value {
        float_hex: String,
    },
}

#[allow(dead_code)]
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct FunLitElt {
    pub indice: ConcreteTerm,
    pub value: ConcreteTerm,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
#[cfg_attr(feature = "serde", serde(tag = "type", content = "val"))]
pub enum ConcreteTerm {
    Var(String),
    Boolean(bool),
    String(String),
    Integer(Integer),
    Real(Real),
    BitVector(BitVector),
    Fraction {
        #[cfg_attr(feature = "serde", serde(rename = "frac_num"))]
        num: Real,
        #[cfg_attr(feature = "serde", serde(rename = "frac_denom"))]
        denom: Real,
        #[cfg_attr(feature = "serde", serde(rename = "frac_verbatim"))]
        verbatim: String,
    },
    Float(Float),
    #[cfg_attr(feature = "serde", serde(rename = "Apply"))]
    App {
        #[cfg_attr(feature = "serde", serde(rename = "app_ls"))]
        ls: String,
        #[cfg_attr(feature = "serde", serde(rename = "app_args"))]
        args: Vec<ConcreteTerm>,
    },
    If {
        #[cfg_attr(feature = "serde", serde(rename = "if"))]
        ift: Box<ConcreteTerm>,
        then: Box<ConcreteTerm>,
        #[cfg_attr(feature = "serde", serde(rename = "else"))]
        elset: Box<ConcreteTerm>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Epsilon"))]
    Eps {
        #[cfg_attr(feature = "serde", serde(rename = "eps_var"))]
        var: String,
        #[cfg_attr(feature = "serde", serde(rename = "eps_t"))]
        t: Box<ConcreteTerm>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "Function"))]
    Fun {
        #[cfg_attr(feature = "serde", serde(rename = "fun_args"))]
        args: Vec<String>,
        #[cfg_attr(feature = "serde", serde(rename = "fun_body"))]
        body: Box<ConcreteTerm>,
    },
    Quant {
        quant: String,
        #[cfg_attr(feature = "serde", serde(rename = "quant_vs"))]
        vs: Vec<String>,
        #[cfg_attr(feature = "serde", serde(rename = "quant_t"))]
        t: Box<ConcreteTerm>,
    },
    Binop {
        binop: String,
        #[cfg_attr(feature = "serde", serde(rename = "binop_t1"))]
        t1: Box<ConcreteTerm>,
        #[cfg_attr(feature = "serde", serde(rename = "binop_t2"))]
        t2: Box<ConcreteTerm>,
    },
    Not(Box<ConcreteTerm>),
    FunctionLiteral {
        #[cfg_attr(feature = "serde", serde(rename = "funliteral_elts"))]
        elts: Vec<FunLitElt>,
        #[cfg_attr(feature = "serde", serde(rename = "funliteral_others"))]
        other: Box<ConcreteTerm>,
    },
    Proj {
        #[cfg_attr(feature = "serde", serde(rename = "proj_name"))]
        name: String,
        #[cfg_attr(feature = "serde", serde(rename = "proj_value"))]
        value: Box<ConcreteTerm>,
    },
    #[cfg_attr(feature = "serde", serde(untagged))]
    Unknown(Json),
}

#[cfg_attr(feature = "serde", derive(Deserialize, Debug))]
pub struct Goal {
    pub term: GoalTerm,
    #[cfg_attr(feature = "serde", serde(alias = "prover-result"))]
    pub prover_result: ProverResult,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct GoalTerm {
    pub loc: Loc,
    #[cfg_attr(feature = "serde", serde(alias = "goal-name"))]
    //Why3 doesn't currently use kebab-case but this might change
    pub goal_name: String,
    pub explanations: Vec<String>,
}
#[allow(dead_code)]
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize))]
pub struct ProverResult {
    pub answer: String,
    #[cfg_attr(feature = "serde", serde(rename = "ce-models"))]
    pub ce_models: Vec<Model>,
    pub time: f32,
    pub step: i32,
}

impl ProverResult {
    pub fn model_elems(&self) -> impl Iterator<Item = &ModelElem> {
        self.ce_models
            .iter()
            .flat_map(|x| match x {
                Model::Model { model, .. } => &**model,
                _ => &[],
            })
            .flat_map(|x| match x {
                Fallible::Ok(x) => &*x.model,
                _ => &[],
            })
            .flat_map(|x| match x {
                Fallible::Ok(x) => &*x.model_elements,
                _ => &[],
            })
            .filter_map(|x| match x {
                Fallible::Ok(x) => Some(x),
                _ => None,
            })
    }
}
