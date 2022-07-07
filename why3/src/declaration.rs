use indexmap::IndexSet;
use std::collections::{BTreeMap, HashMap};

use crate::exp::{Exp, ExpMutVisitor};
use crate::mlcfg::{Block, BlockId};
use crate::ty::Type;
use crate::*;

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Module {
    pub name: Ident,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Scope {
    pub name: Ident,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Decl {
    FunDecl(CfgFunction),
    Let(LetDecl),
    LetFun(LetFun),
    ValDecl(ValKind),
    LogicDecl(Logic),
    Scope(Scope),
    Module(Module),
    TyDecl(TyDecl),
    PredDecl(Predicate),
    Clone(DeclClone),
    UseDecl(Use),
    Axiom(Axiom),
    Goal(Goal),
    // ConstantDecl(Constant),
}

impl Decl {
    pub fn module_like(&self) -> bool {
        matches!(self, Self::Scope(_) | Self::Module(_))
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
    Span(String, usize, usize, usize, usize), // file, start line, start col, end line, end col
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Signature {
    pub name: Ident,
    pub attrs: Vec<Attribute>,
    pub retty: Option<Type>,
    pub args: Vec<(Ident, Type)>,
    pub contract: Contract,
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
    pub vars: Vec<(bool, Ident, Type)>,
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
    pub fields: Vec<Type>,
}

impl TyDecl {
    pub fn used_types(&self) -> IndexSet<QName> {
        let mut used = IndexSet::new();
        match &self {
            TyDecl::Adt { tys } => {
                for AdtDecl { constrs, .. } in tys {
                    for cons in constrs {
                        for ty in &cons.fields {
                            ty.find_used_types(&mut used);
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
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Use {
    pub name: QName,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Axiom {
    pub name: Ident,
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
    pub sig: Signature,
    pub rec: bool,
    pub constant: bool,
    pub body: Exp,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct LetFun {
    pub sig: Signature,
    pub rec: bool,
    pub ghost: bool,
    pub body: Exp,
}
