use serde::Deserialize;
use serde_json::Value as Json;
use std::{
    fmt::{Debug, Formatter},
};

#[derive(Deserialize)]
#[serde(untagged)]
pub enum Loc {
    Span(Why3Span),
    Other(Json),
}

#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
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
            Loc::Span(Why3Span{file_name, start_line, start_char, end_line, end_char }) => {
                write!(f, "[#\"{file_name}\" {start_line} {start_char} {end_line} {end_char}]")
            }
            _ => write!(f, "[#???]")
        }
    }
}

#[derive(Deserialize, Debug)]
#[serde(untagged)]
pub enum Fallible<T> {
    Ok(T),
    Err(Json),
}

#[derive(Deserialize, Debug)]
#[serde(untagged)]
pub enum Model {
    Model { answer: String, model: Vec<Fallible<Model2>> },
    Unknown(Json),
}

#[derive(Deserialize, Debug)]
pub struct Model2 {
    pub filename: String,
    pub model: Vec<Fallible<Model3>>,
}

#[derive(Deserialize, Debug)]
pub struct Model3 {
    pub is_vc_line: bool,
    pub line: String,
    pub model_elements: Vec<Fallible<ModelElem>>,
}

#[derive(Deserialize, Debug)]
pub struct LSymbol {
    pub name: String,
    pub attrs: Vec<String>,
    pub loc: Loc,
}

#[derive(Deserialize, Debug)]
pub struct ModelElem {
    pub attrs: Vec<String>,
    pub kind: String,
    pub location: Loc,
    pub lsymbol: LSymbol,
    pub value: Value,
}

#[derive(Deserialize, Debug)]
pub struct Value {
    pub value_concrete_term: ConcreteTerm,
    pub value_term: Term,
    pub value_type: Type,
}

#[derive(Deserialize)]
pub enum Type {
    #[serde(rename = "Tyvar")]
    Var(String),
    #[serde(rename = "Tyapp")]
    App { ty_symbol: String, ty_args: Vec<Type> },
    #[serde(untagged)]
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

#[derive(Deserialize, Debug)]
pub struct VSymbol {
    pub vs_name: String,
    pub vs_type: Type,
}

#[derive(Deserialize, Debug)]
pub enum TBool {
    #[serde(rename = "Ttrue")]
    True,
    #[serde(rename = "Tfalse")]
    False,
}

#[derive(Deserialize, Debug)]
pub enum Term {
    #[serde(rename = "Tvar")]
    Var(VSymbol),
    #[serde(rename = "Tconst")]
    Const {
        #[serde(rename = "const_type")]
        ty: String,
        #[serde(rename = "const_value")]
        val: String,
    },
    #[serde(rename = "Tapp")]
    App {
        #[serde(rename = "app_ls")]
        ls: String,
        #[serde(rename = "app_args")]
        args: Vec<Term>,
    },
    #[serde(rename = "Tif")]
    If {
        #[serde(rename = "if")]
        ift: Box<Term>,
        then: Box<Term>,
        #[serde(rename = "else")]
        elset: Box<Term>,
    },
    #[serde(rename = "Teps")]
    Eps {
        #[serde(rename = "eps_vs")]
        vs: VSymbol,
        #[serde(rename = "eps_t")]
        t: Box<Term>,
    },
    #[serde(rename = "Tfun")]
    Fun {
        #[serde(rename = "fun_args")]
        args: Vec<VSymbol>,
        #[serde(rename = "fun_body")]
        body: Box<Term>,
    },
    #[serde(rename = "Tquant")]
    Quant {
        quant: String,
        #[serde(rename = "quant_vs")]
        vs: Vec<VSymbol>,
        #[serde(rename = "quant_t")]
        t: Box<Term>,
    },
    #[serde(rename = "Tbinop")]
    Binop {
        binop: String,
        #[serde(rename = "binop_t1")]
        t1: Box<Term>,
        #[serde(rename = "binop_t2")]
        t2: Box<Term>,
    },
    #[serde(rename = "Tnot")]
    Not(Box<Term>),
    #[serde(rename = "Tlet")]
    Let(String),
    #[serde(rename = "Tcase")]
    Case(String),
    #[serde(untagged)]
    Bool(TBool),
    #[serde(untagged)]
    Unknown(Json),
}

#[derive(Deserialize, Debug)]
pub struct BitVector {
    pub bv_value_as_decimal: String,
    pub bv_length: u32,
    pub bv_verbatim: String,
}

#[derive(Deserialize, Debug)]
pub struct Real {
    pub real_value: String,
    pub real_verbatim: String,
}

#[derive(Deserialize)]
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

#[derive(Deserialize, Debug)]
pub enum Float {
    Infinity,
    #[serde(rename = "Plus_zero")]
    PlusZero,
    #[serde(rename = "Minus_zero")]
    MinusZero,
    #[serde(rename = "Float_value")]
    Value {
        float_hex: String,
    },
}

#[allow(dead_code)]
#[derive(Deserialize, Debug)]
pub struct FunLitElt {
    pub indice: ConcreteTerm,
    pub value: ConcreteTerm,
}

#[derive(Deserialize, Debug)]
#[serde(tag = "type", content = "val")]
pub enum ConcreteTerm {
    Var(String),
    Boolean(bool),
    String(String),
    Integer(Integer),
    Real(Real),
    BitVector(BitVector),
    Fraction {
        #[serde(rename = "frac_num")]
        num: Real,
        #[serde(rename = "frac_num")]
        denom: Real,
        #[serde(rename = "frac_verbatim")]
        verbatim: String,
    },
    Float(Float),
    #[serde(rename = "Apply")]
    App {
        #[serde(rename = "app_ls")]
        ls: String,
        #[serde(rename = "app_args")]
        args: Vec<ConcreteTerm>,
    },
    If {
        #[serde(rename = "if")]
        ift: Box<ConcreteTerm>,
        then: Box<ConcreteTerm>,
        #[serde(rename = "else")]
        elset: Box<ConcreteTerm>,
    },
    #[serde(rename = "Epsilon")]
    Eps {
        #[serde(rename = "eps_var")]
        var: String,
        #[serde(rename = "eps_t")]
        t: Box<ConcreteTerm>,
    },
    #[serde(rename = "Function")]
    Fun {
        #[serde(rename = "fun_args")]
        args: Vec<String>,
        #[serde(rename = "fun_body")]
        body: Box<ConcreteTerm>,
    },
    Quant {
        quant: String,
        #[serde(rename = "quant_vs")]
        vs: Vec<String>,
        #[serde(rename = "quant_t")]
        t: Box<ConcreteTerm>,
    },
    Binop {
        binop: String,
        #[serde(rename = "binop_t1")]
        t1: Box<ConcreteTerm>,
        #[serde(rename = "binop_t2")]
        t2: Box<ConcreteTerm>,
    },
    Not(Box<ConcreteTerm>),
    FunctionLiteral {
        #[serde(rename = "funliteral_elts")]
        elts: Vec<FunLitElt>,
        #[serde(rename = "funliteral_others")]
        other: Box<ConcreteTerm>,
    },
    Proj {
        #[serde(rename = "proj_name")]
        name: String,
        #[serde(rename = "proj_value")]
        value: Box<ConcreteTerm>,
    },
    #[serde(untagged)]
    Unknown(Json),
}

#[derive(Deserialize)]
pub struct Goal {
    pub term: GoalTerm,
    #[serde(alias = "prover-result")]
    pub prover_result: ProverResult,
}

#[derive(Deserialize, Debug)]
pub struct GoalTerm {
    pub loc: Loc,
    #[serde(alias = "goal-name")] //Why3 doesn't currently use kebab-case but this might change
    pub goal_name: String,
    pub explanations: Vec<String>,
}
#[allow(dead_code)]
#[derive(Deserialize, Debug)]
pub struct ProverResult {
    pub answer: String,
    #[serde(rename = "ce-models")]
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
