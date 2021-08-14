use std::iter::FromIterator;

use ena::unify::{EqUnifyValue, UnifyKey};
use indexmap::IndexMap;

// AST definitions for Creusot specification language expressions

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Name {
    Path {
        path: Vec<String>,
        name: String,
        // an identifier that can be used to rapidly compare paths
        id: u64,
    },
    Ident(String),
}

#[derive(Debug)]
pub enum Term {
    Match { expr: Box<Term>, arms: Vec<MatchArm> },
    If { cond: Box<Term>, then_branch: Box<Term>, else_branch: Box<Term> },
    Binary { left: Box<Term>, op: BinOp, right: Box<Term> },
    Lit { lit: Literal },
    Variable { path: Name },
    Forall { args: Vec<(Ident, Type)>, body: Box<Term> },
    Exists { args: Vec<(Ident, Type)>, body: Box<Term> },
    Tuple { elems: Vec<Term> },
    Let { pat: Pattern, arg: Box<Term>, body: Box<Term> },
    Call { func: Name, args: Vec<Term> },
    Unary { op: UnOp, expr: Box<Term> },
    Cast { expr: Box<Term>, ty: Type },
    Absurd,
}

impl Term {
    pub fn unit() -> Self {
        Term::Tuple { elems: vec![] }
    }
}

#[derive(Debug)]
pub enum Literal {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Usize(usize),
    // TODO make this bigint
    Int(i128),
    F32(f32),
    F64(f64),
    Bool(bool),
}

#[derive(Debug)]
pub enum DerefKind {
    Box,
    Ref(RefKind),
}

#[derive(Debug)]
pub enum UnOp {
    Deref(Option<DerefKind>),
    Final,
    Neg,
    Not,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Ne,
    Le,
    Ge,
    Gt,
    Lt,
    And,
    Or,
    Impl,
}

#[derive(Debug)]
pub struct MatchArm {
    pub pat: Pattern,
    pub body: Box<Term>,
}

#[derive(Debug)]
pub enum Pattern {
    Var(Ident),
    Struct { path: Name, fields: Vec<(Ident, Pattern)> },
    TupleStruct { path: Name, fields: Vec<Pattern> },
    Tuple { fields: Vec<Pattern> },
    Boolean(bool),
    Wild,
}

// We only keep around immutable references for debugging purposes
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefKind {
    Mut,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Size {
    Eight,
    Sixteen,
    ThirtyTwo,
    SixtyFour,
    Unknown,
    Mach,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LitTy {
    Signed(Size),
    Unsigned(Size),
    Integer,
    Float,
    Double,
    Boolean,
}

impl LitTy {
    pub const I8: Self = Self::Signed(Size::Eight);
    pub const I16: Self = Self::Signed(Size::Sixteen);
    pub const I32: Self = Self::Signed(Size::ThirtyTwo);
    pub const I64: Self = Self::Signed(Size::SixtyFour);
    pub const ISIZE: Self = Self::Signed(Size::Mach);

    pub const U8: Self = Self::Unsigned(Size::Eight);
    pub const U16: Self = Self::Unsigned(Size::Sixteen);
    pub const U32: Self = Self::Unsigned(Size::ThirtyTwo);
    pub const U64: Self = Self::Unsigned(Size::SixtyFour);
    pub const USIZE: Self = Self::Unsigned(Size::Mach);
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub struct TyVar(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub struct TyUnk(u32);

impl TyUnk {
    pub fn zonk(self) -> TyVar {
        TyVar(self.0)
    }
}

impl UnifyKey for TyUnk {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        TyUnk(u)
    }

    fn tag() -> &'static str {
        "unknown type"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Path { path: Name },
    Box { ty: Box<Type> },
    Reference { kind: RefKind, ty: Box<Type> },
    Tuple { elems: Vec<Type> },
    Function { args: Vec<Type>, res: Box<Type> },
    App { func: Box<Type>, args: Vec<Type> },
    Lit(LitTy),
    Var(TyVar),
    Unknown(TyUnk),
}

impl EqUnifyValue for Type {}

pub struct VarSubst(IndexMap<TyVar, Type>);
impl FromIterator<(TyVar, Type)> for VarSubst {
    fn from_iter<T: IntoIterator<Item = (TyVar, Type)>>(iter: T) -> Self {
        VarSubst(IndexMap::from_iter(iter))
    }
}

pub trait Substitution {
    fn subst(&self, ty: &mut Type);
}

impl Substitution for VarSubst {
    fn subst(&self, ty: &mut Type) {
        match ty {
            Type::Box { ty } => self.subst(ty),
            Type::Reference { ty, .. } => self.subst(ty),
            Type::Tuple { elems } => elems.iter_mut().for_each(|e| self.subst(e)),
            Type::Var(v) => {
                if let Some(t) = self.0.get(v) {
                    *ty = t.clone();
                }
            }
            Type::Function { args, res } => {
                args.iter_mut().for_each(|t| self.subst(t));
                self.subst(res);
            }
            Type::App { box func, args } => {
                self.subst(func);
                args.iter_mut().for_each(|t| self.subst(t));
            }
            Type::Lit(_) => {}
            Type::Path { .. } => {}
            Type::Unknown(_) => {}
        }
    }
}

impl Type {
    pub const BOOLEAN: Self = Self::Lit(LitTy::Boolean);

    pub fn is_numeric(&self) -> bool {
        use LitTy::*;
        matches!(
            self,
            Type::Lit(Signed(_))
                | Type::Lit(Unsigned(_))
                | Type::Lit(Float)
                | Type::Lit(Double)
                | Type::Lit(Integer)
        )
    }

    pub fn is_reference(&self) -> bool {
        matches!(self, Type::Reference { .. })
    }

    pub fn fvs(&self) -> Vec<TyVar> {
        let mut v = Vec::new();
        self.fvs_(&mut v);

        v
    }

    fn fvs_(&self, v: &mut Vec<TyVar>) {
        use Type::*;
        match self {
            Type::Path { .. } => {}
            Box { ty } => ty.fvs_(v),
            Reference { ty, .. } => ty.fvs_(v),
            Tuple { elems } => {
                elems.iter().for_each(|e| e.fvs_(v));
            }
            Function { args, res } => {
                args.iter().for_each(|a| a.fvs_(v));
                res.fvs_(v);
            }
            App { func, args } => {
                args.iter().for_each(|a| a.fvs_(v));
                func.fvs_(v);
            }
            Lit(_) => {}
            Var(var) => {
                v.push(*var);
            }
            Unknown(_) => {}
        }
    }
}
