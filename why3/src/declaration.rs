use indexmap::IndexSet;
use std::collections::{BTreeMap, HashMap};

use crate::{
    exp::{Binder, Exp, ExpMutVisitor, Trigger},
    mlcfg::{Block, BlockId},
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
pub struct Scope {
    pub name: Ident,
    pub decls: Vec<Decl>,
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
    CfgDecl(CfgFunction),
    Let(LetDecl),
    ValDecl(ValDecl),
    LogicDefn(Logic),
    Scope(Scope),
    Module(Module),
    TyDecl(TyDecl),
    PredDecl(Predicate),
    Clone(DeclClone),
    UseDecl(Use),
    Axiom(Axiom),
    Goal(Goal),
    ConstantDecl(Constant),
    Coma(coma::Defn),
    LetSpans(Vec<Span>),
    Meta(Meta),
    Comment(String),
}

impl Decl {
    pub fn module_like(&self) -> bool {
        matches!(self, Self::Scope(_) | Self::Module(_))
    }

    pub fn val(sig: Signature) -> Self {
        Decl::ValDecl(ValDecl { ghost: false, val: true, kind: None, sig })
    }

    pub fn val_pred(mut sig: Signature) -> Self {
        sig.retty = None;
        Decl::ValDecl(ValDecl { ghost: false, val: true, kind: Some(LetKind::Predicate), sig })
    }

    pub fn val_fn(sig: Signature) -> Self {
        Decl::ValDecl(ValDecl { ghost: false, val: true, kind: Some(LetKind::Function), sig })
    }

    pub fn function(sig: Signature, body: Option<Exp>) -> Self {
        match body {
            Some(body) => Decl::LogicDefn(Logic { sig, body }),
            None => Decl::ValDecl(ValDecl {
                ghost: false,
                val: false,
                kind: Some(LetKind::Function),
                sig,
            }),
        }
    }

    pub fn val_function(sig: Signature, body: Option<Exp>) -> Self {
        match body {
            Some(body) => Decl::Let(LetDecl {
                kind: Some(LetKind::Function),
                sig,
                rec: false,
                ghost: false,
                body,
            }),
            None => Decl::ValDecl(ValDecl {
                ghost: false,
                val: true,
                kind: Some(LetKind::Function),
                sig,
            }),
        }
    }

    pub fn val_predicate(sig: Signature, body: Option<Exp>) -> Self {
        match body {
            Some(body) => Decl::Let(LetDecl {
                kind: Some(LetKind::Predicate),
                sig,
                rec: false,
                ghost: false,
                body,
            }),
            None => Decl::ValDecl(ValDecl {
                ghost: false,
                val: true,
                kind: Some(LetKind::Function),
                sig,
            }),
        }
    }

    pub fn predicate(mut sig: Signature, body: Option<Exp>) -> Self {
        sig.retty = None;

        match body {
            Some(body) => Decl::PredDecl(Predicate { sig, body }),
            None => Decl::ValDecl(ValDecl {
                ghost: false,
                val: false,
                kind: Some(LetKind::Predicate),
                sig,
            }),
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
        coma::Term::Attr(Attribute::Attr(self.expl), Box::new(self.exp))
    }
    pub fn unlabelled_exp(self) -> Exp {
        self.exp
    }
}

#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Contract {
    pub requires: Vec<Condition>,
    pub ensures: Vec<Condition>,
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
        let mut ensures = self.ensures.iter().map(|cond| cond.exp.clone());
        let Some(mut postcond) = ensures.next() else { return Exp::mk_true() };
        postcond = ensures.fold(postcond, Exp::lazy_conj);
        postcond.reassociate();
        postcond
    }

    pub fn ensures_conj_labelled(&self) -> Exp {
        let mut ensures = self.ensures.iter().cloned().map(Condition::labelled_exp);
        let Some(mut postcond) = ensures.next() else { return Exp::mk_true() };
        postcond = ensures.fold(postcond, Exp::lazy_conj);
        postcond.reassociate();
        postcond
    }

    pub fn requires_conj(&self) -> Exp {
        let mut requires = self.requires.iter().map(|cond| cond.exp.clone());
        let Some(mut postcond) = requires.next() else { return Exp::mk_true() };
        postcond = requires.fold(postcond, Exp::lazy_conj);
        postcond.reassociate();
        postcond
    }

    pub fn requires_conj_labelled(&self) -> Exp {
        let mut requires = self.requires.iter().cloned().map(Condition::labelled_exp);
        let Some(mut postcond) = requires.next() else { return Exp::mk_true() };
        postcond = requires.fold(postcond, Exp::lazy_conj);
        postcond.reassociate();
        postcond
    }

    pub fn requires_implies(&self, conclusion: Exp) -> Exp {
        let requires = self.requires.iter().map(|cond| cond.exp.clone());
        requires.rfold(conclusion, |acc, arg| arg.implies(acc))
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
            req_visitor.visit_mut(&mut req.exp);
        }

        for ens in self.ensures.iter_mut() {
            ens_visitor.visit_mut(&mut ens.exp);
        }

        for var in self.variant.iter_mut() {
            var_visitor.visit_mut(var);
        }
    }

    pub fn qfvs(&self) -> IndexSet<QName> {
        let mut qfvs = IndexSet::new();

        for req in &self.requires {
            qfvs.extend(req.exp.qfvs());
        }

        for ens in &self.ensures {
            qfvs.extend(ens.exp.qfvs());
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
pub struct Logic {
    pub sig: Signature,
    pub body: Exp,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct CfgFunction {
    pub sig: Signature,
    pub rec: bool,
    pub constant: bool,
    pub vars: Vec<(bool, Ident, Type, Option<Exp>)>,
    pub entry: Block,
    pub blocks: BTreeMap<BlockId, Block>,
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
    pub constrs: Vec<ConstructorDecl>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct ConstructorDecl {
    pub name: Ident,
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Field {
    pub ghost: bool,
    pub ty: Type,
}

impl TyDecl {
    pub fn used_types(&self) -> IndexSet<QName> {
        let mut used = IndexSet::new();
        match &self {
            TyDecl::Adt { tys } => {
                for AdtDecl { constrs, .. } in tys {
                    for cons in constrs {
                        for ty in &cons.fields {
                            ty.ty.find_used_types(&mut used);
                        }
                    }
                }
            }
            TyDecl::Alias { alias, .. } => {
                alias.find_used_types(&mut used);
            }
            TyDecl::Opaque { .. } => {}
        }
        used
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct DeclClone {
    pub name: QName,
    pub subst: Vec<CloneSubst>,
    pub kind: CloneKind,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum CloneKind {
    Bare,
    Named(Ident),
    Export,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum CloneSubst {
    Type(QName, Type),
    Val(QName, QName),
    Predicate(QName, QName),
    Function(QName, QName),
    Axiom(Option<QName>),
}

impl CloneSubst {
    pub fn self_subst(ty: Type) -> Self {
        Self::Type("self".into(), ty)
    }
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
pub struct ValDecl {
    pub ghost: bool,
    pub val: bool,
    pub kind: Option<LetKind>,
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

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct LetDecl {
    pub kind: Option<LetKind>,
    pub sig: Signature,
    pub rec: bool,
    pub ghost: bool,
    pub body: Exp,
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum LetKind {
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
