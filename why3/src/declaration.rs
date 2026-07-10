use crate::{coma::Defn, exp::Exp, ty::Type, *};

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Module {
    pub name: Symbol,
    pub decls: Box<[Decl]>,
    pub attrs: Vec<Attribute>,
    // Meta data stored in comments
    // Stores a pretty representation of the impl
    pub meta: Option<String>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Span {
    pub name: Ident,
    pub path: String,
    pub start_line: usize,
    pub start_column: usize,
    pub end_line: usize,
    pub end_column: usize,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Decl {
    LogicDecl(LogicDecl),
    LogicDefn(LogicDefn),
    TyDecl(TyDecl),
    PredDecl(Predicate),
    UseDecls(Box<[Use]>),
    Axiom(Axiom),
    Goal(Goal),
    ConstantDecl(Constant),
    Coma(Defn),
    LetSpans(Box<[Span]>),
    Meta(Meta),
    Comment(String),
}

impl Decl {
    pub fn function(sig: Signature, body: Option<Exp>) -> Self {
        match body {
            Some(body) => Decl::LogicDefn(LogicDefn { sig, body }),
            None => Decl::LogicDecl(LogicDecl { kind: Some(DeclKind::Function), sig }),
        }
    }

    pub fn predicate(mut sig: Signature, body: Option<Exp>) -> Self {
        sig.retty = None;

        match body {
            Some(body) => Decl::PredDecl(Predicate { sig, body }),
            None => Decl::LogicDecl(LogicDecl { kind: Some(DeclKind::Predicate), sig }),
        }
    }
}

/// A term with an "expl:" label (includes the "expl:" prefix)
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Condition {
    pub exp: Exp,
    /// Label including the "expl:" prefix.
    pub expl: String,
}

impl Condition {
    pub fn labelled_exp(self) -> Exp {
        self.exp
            .with_attr(Attribute::Attr(self.expl))
            .with_attr(Attribute::Attr("stop_split".into()))
    }

    pub fn plain_exp(self) -> Exp {
        self.exp
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Attribute {
    Attr(String),
    NamedSpan(Ident),
    Span(String, usize, usize, usize, usize), // file, start line, start col, end line, end col
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Signature {
    pub name: Ident,
    pub attrs: Vec<Attribute>,
    pub retty: Option<Type>,
    pub args: Box<[(Ident, Type)]>,
}

impl Signature {
    pub fn constant(name: Ident, ty: Type) -> Self {
        Self { name, attrs: vec![], retty: Some(ty), args: [].into() }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct LogicDefn {
    pub sig: Signature,
    pub body: Exp,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Predicate {
    pub sig: Signature,
    pub body: Exp,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum TyDecl {
    Adt { tys: Box<[AdtDecl]> },
    Alias { ty_name: Ident, ty_params: Box<[Ident]>, alias: Type },
    Opaque { ty_name: Ident, ty_params: Box<[Ident]> },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct AdtDecl {
    pub ty_name: Ident,
    pub ty_params: Box<[Ident]>,
    pub sumrecord: SumRecord,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum SumRecord {
    Sum(Box<[ConstructorDecl]>),
    Record(Box<[FieldDecl]>),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct ConstructorDecl {
    pub name: Ident,
    pub fields: Box<[Type]>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct FieldDecl {
    pub name: Ident,
    pub ty: Type,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum ValKind {
    Val { sig: Signature },
    Predicate { sig: Signature },
    Function { sig: Signature },
    ValFunction { sig: Signature },
    ValPredicate { sig: Signature },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct LogicDecl {
    pub kind: Option<DeclKind>,
    pub sig: Signature,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Use {
    pub name: Box<[Symbol]>,
    pub export: bool,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Axiom {
    pub name: Ident,
    pub rewrite: bool,
    pub axiom: Exp,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Goal {
    pub name: Ident,
    pub goal: Exp,
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum DeclKind {
    Function,
    Predicate,
    Constant,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Constant {
    pub name: Ident,
    pub type_: Type,
    pub body: Option<Exp>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Meta {
    pub name: MetaIdent,
    pub args: Box<[MetaArg]>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct MetaIdent(pub Symbol);

// meta_arg:
// | TYPE      ty      { Mty $2 }
// | CONSTANT  qualid  { Mfs $2 }
// | FUNCTION  qualid  { Mfs $2 }
// | PREDICATE qualid  { Mps $2 }
// | AXIOM     qualid  { Max $2 }
// | LEMMA     qualid  { Mlm $2 }
// | GOAL      qualid  { Mgl $2 }
// | VAL       qualid  { Mval $2 }
// | STRING            { Mstr $1 }
// | INTEGER           { Mint (Number.to_small_integer $1) }

/// Example: in `meta "rewrite_def" function f`, `function` is a `Keyword` and `f` is an `Ident`
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum MetaArg {
    Integer(i128),
    String(String),
    Keyword(String),
    Name(Name),
}
