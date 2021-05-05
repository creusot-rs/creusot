use std::collections::{HashMap, BTreeMap, HashSet};

use crate::mlcfg::{Exp, LocalIdent, Type, QName, BlockId, Block};

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
    LogicDecl(Logic),
    Scope(Scope),
    Module(Module),
    TyDecl(TyDecl),
    PredDecl(Predicate),
}

#[derive(Debug, Default)]
pub struct Contract {
    pub requires: Vec<Exp>,
    pub ensures: Vec<Exp>,
    pub variant: Option<Exp>,
}

impl Contract {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn subst(&mut self, subst: &HashMap<LocalIdent, Exp>) {
        for req in self.requires.iter_mut() {
            req.subst(subst);
        }
        for ens in self.ensures.iter_mut() {
            ens.subst(subst);
        }
        if let Some(variant) = &mut self.variant {
            variant.subst(subst);
        }
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
