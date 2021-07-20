use std::collections::{BTreeMap, HashMap, HashSet};

use crate::mlcfg::{Block, BlockId, Exp, LocalIdent, QName, Type};

#[derive(Debug)]
pub struct Module {
    pub name: String,
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
pub struct Scope {
    pub name: String,
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
pub enum Decl {
    FunDecl(CfgFunction),
    ValDecl(Val),
    LogicDecl(Logic),
    Scope(Scope),
    Module(Module),
    TyDecl(TyDecl),
    PredDecl(Predicate),
    Clone(DeclClone),
    UseDecl(Use),
}

impl Decl {
    pub fn module_like(&self) -> bool {
        matches!(self, Self::Scope(_) | Self::Module(_))
    }
}

#[derive(Debug, Default)]
pub struct Contract {
    pub requires: Vec<Exp>,
    pub ensures: Vec<Exp>,
    pub variant: Vec<Exp>,
}

impl Contract {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn extend(&mut self, other: Contract) {
        self.requires.extend(other.requires);
        self.ensures.extend(other.ensures);
        self.variant.extend(other.variant);
    }

    pub fn subst(&mut self, subst: &HashMap<LocalIdent, Exp>) {
        for req in self.requires.iter_mut() {
            req.subst(subst);
        }

        for ens in self.ensures.iter_mut() {
            ens.subst(subst);
        }

        for var in self.variant.iter_mut() {
            var.subst(subst);
        }
    }

    pub fn qfvs(&self) -> HashSet<QName> {
        let mut qfvs = HashSet::new();

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

#[derive(Debug)]
pub struct Logic {
    pub name: QName,
    pub retty: Type,
    pub args: Vec<(LocalIdent, Type)>,
    pub body: Exp,
    pub contract: Contract,
}

#[derive(Debug)]
pub struct CfgFunction {
    pub name: QName,
    pub retty: Type,
    pub args: Vec<(LocalIdent, Type)>,
    pub vars: Vec<(LocalIdent, Type)>,
    pub entry: Block,
    pub blocks: BTreeMap<BlockId, Block>,
    pub contract: Contract,
}

#[derive(Debug)]
pub struct Predicate {
    pub name: QName,
    pub args: Vec<(LocalIdent, Type)>,
    pub body: Exp,
}

#[derive(Debug)]
pub struct TyDecl {
    pub ty_name: QName,
    pub ty_params: Vec<String>,
    pub ty_constructors: Vec<(String, Vec<Type>)>,
}

impl TyDecl {
    pub fn used_types(&self) -> HashSet<QName> {
        let mut used = HashSet::new();
        for (_, var_decl) in &self.ty_constructors {
            for ty in var_decl {
                ty.find_used_types(&mut used);
            }
        }
        used
    }
}

#[derive(Debug)]
pub struct DeclClone {
    pub name: QName,
    pub subst: Vec<CloneSubst>,
    pub as_nm: Option<String>,
}

#[derive(Debug)]
pub enum CloneSubst {
    Type(LocalIdent, Type),
    Val(LocalIdent, QName),
}

impl CloneSubst {
    pub fn self_subst(ty: Type) -> Self {
        Self::Type(LocalIdent::Name("self".into()), ty)
    }
}

#[derive(Debug)]
pub struct Val {
    pub name: QName,
    pub contract: Contract,
    pub params: Vec<(LocalIdent, Type)>,
    pub retty: Type,
}

#[derive(Debug)]
pub struct Use {
    pub name: QName,
}
