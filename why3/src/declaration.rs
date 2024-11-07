use indexmap::IndexSet;
use std::collections::HashMap;

use crate::{
    coma::Defn,
    exp::{Binder, Exp, ExpMutVisitor, Trigger},
    ty::Type,
    *,
};

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Module {
    pub name: Ident,
    pub decls: Vec<Decl>,
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
    UseDecl(Use),
    Axiom(Axiom),
    Goal(Goal),
    ConstantDecl(Constant),
    Coma(Defn),
    LetSpans(Vec<Span>),
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

#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Contract {
    pub requires: Vec<Exp>,
    pub ensures: Vec<Exp>,
    pub variant: Vec<Exp>,
}

impl Contract {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.variant.is_empty()
    }

    pub fn extend(&mut self, other: Contract) {
        self.requires.extend(other.requires);
        self.ensures.extend(other.ensures);
        self.variant.extend(other.variant);
    }

    pub fn ensures_conj(&self) -> Exp {
        let mut ensures = self.ensures.clone();

        let postcond = ensures.pop().unwrap_or(Exp::mk_true());
        let mut postcond = ensures.into_iter().rfold(postcond, Exp::lazy_conj);
        postcond.reassociate();
        postcond
    }

    pub fn requires_conj(&self) -> Exp {
        let mut requires = self.requires.clone();

        let precond = requires.pop().unwrap_or(Exp::mk_true());
        let mut precond = requires.into_iter().rfold(precond, Exp::lazy_conj);
        precond.reassociate();
        precond
    }

    pub fn subst(&mut self, subst: &HashMap<Ident, Exp>) {
        self.visit_mut(subst, subst, subst);
    }

    pub fn visit_mut<T: ExpMutVisitor>(
        &mut self,
        mut req_visitor: T,
        mut ens_visitor: T,
        mut var_visitor: T,
    ) {
        for req in self.requires.iter_mut() {
            req_visitor.visit_mut(req);
        }

        for ens in self.ensures.iter_mut() {
            ens_visitor.visit_mut(ens);
        }

        for var in self.variant.iter_mut() {
            var_visitor.visit_mut(var);
        }
    }

    pub fn qfvs(&self) -> IndexSet<QName> {
        let mut qfvs = IndexSet::new();

        for req in &self.requires {
            qfvs.extend(req.qfvs());
        }

        for ens in &self.ensures {
            qfvs.extend(ens.qfvs());
        }

        for var in &self.variant {
            qfvs.extend(var.qfvs());
        }

        qfvs
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Attribute {
    Attr(String),
    NamedSpan(String),
    Span(String, usize, usize, usize, usize), // file, start line, start col, end line, end col
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Signature {
    pub name: Ident,
    pub trigger: Option<Trigger>, // None means we should use the "simple_trigger"
    pub attrs: Vec<Attribute>,
    pub retty: Option<Type>,
    pub args: Vec<Binder>,
    pub contract: Contract,
}

impl Signature {
    pub fn uses_simple_triggers(&self) -> bool {
        self.trigger.is_some()
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
    Adt { tys: Vec<AdtDecl> },
    Alias { ty_name: Ident, ty_params: Vec<Ident>, alias: Type },
    Opaque { ty_name: Ident, ty_params: Vec<Ident> },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct AdtDecl {
    pub ty_name: Ident,
    pub ty_params: Vec<Ident>,
    pub sumrecord: SumRecord,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum SumRecord {
    Sum(Vec<ConstructorDecl>),
    Record(Vec<FieldDecl>),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct ConstructorDecl {
    pub name: Ident,
    pub fields: Vec<Type>,
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

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Use {
    pub name: QName,
    pub as_: Option<Ident>,
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
    pub args: Vec<MetaArg>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum MetaIdent {
    String(String),
    Ident(Ident),
}

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

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum MetaArg {
    Integer(i128),
}
