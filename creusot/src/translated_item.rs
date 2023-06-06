use indexmap::IndexMap;
use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Module};

pub enum TranslatedItem {
    Logic {
        // A module which contains the contract with an opaque function symbol
        interface: Module,
        // A dummy module which just contains the function symbol with no contract
        stub: Module,
        // A module which contains the function body but uses stubs for all called functions
        modl: Module,
        // A module which contains the function body (and contract) but uses the actual bodies of all called functions
        proof_modl: Option<Module>,
        has_axioms: bool,
    },
    Closure {
        interface: Vec<Module>,
        modl: Option<Module>,
    },
    Program {
        interface: Module,
        modl: Option<Module>,
    },
    Trait {},
    Impl {
        modl: Module, // Refinement of traits,
    },
    AssocTy {
        modl: Module,
    },
    Constant {
        stub: Module,
        modl: Module,
    },
    // Types can not have dependencies yet, as Why3 does not yet have applicative clones
    Type {
        modl: Vec<Module>,
        accessors: IndexMap<DefId, IndexMap<DefId, Decl>>,
    },
    TyInv {
        modl: Module,
    },
}

impl<'a> TranslatedItem {
    pub(crate) fn has_axioms(&self) -> bool {
        match self {
            TranslatedItem::Logic { has_axioms, .. } => *has_axioms,
            TranslatedItem::Program { .. } => false,
            _ => false,
        }
    }

    pub(crate) fn modules(self) -> Box<dyn Iterator<Item = Module>> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Logic { interface, stub, modl, proof_modl, .. } => Box::new(
                iter::once(stub)
                    .chain(iter::once(interface))
                    .chain(iter::once(modl))
                    .chain(proof_modl.into_iter()),
            ),
            Program { interface, modl, .. } => {
                Box::new(iter::once(interface).chain(modl.into_iter()))
            }
            Trait { .. } => Box::new(iter::empty()),
            Impl { modl, .. } => Box::new(iter::once(modl)),
            AssocTy { modl, .. } => Box::new(iter::once(modl)),
            Constant { stub, modl, .. } => {
                Box::new(std::iter::once(stub).chain(std::iter::once(modl)))
            }
            Type { mut modl, accessors, .. } => {
                modl[0].decls.extend(accessors.values().flat_map(|v| v.values()).cloned());

                Box::new(modl.into_iter())
            }
            Closure { interface, modl } => Box::new(interface.into_iter().chain(modl.into_iter())),
            TyInv { modl } => Box::new(iter::once(modl)),
        }
    }

    pub(crate) fn interface(self) -> Box<dyn Iterator<Item = Module>> {
        match self {
            TranslatedItem::Logic { interface, modl, stub, .. } => Box::new(
                std::iter::once(stub)
                    .chain(std::iter::once(interface))
                    .chain(std::iter::once(modl)),
            ),
            TranslatedItem::Program { interface, .. } => Box::new(std::iter::once(interface)),
            TranslatedItem::Trait { .. } => Box::new(std::iter::empty()),
            TranslatedItem::Impl { modl, .. } => Box::new(std::iter::once(modl)),
            TranslatedItem::AssocTy { modl, .. } => Box::new(std::iter::once(modl)),
            TranslatedItem::Constant { stub, modl, .. } => {
                Box::new(std::iter::once(stub).chain(std::iter::once(modl)))
            }
            TranslatedItem::Type { .. } => self.modules(),
            TranslatedItem::Closure { interface, modl: _ } => Box::new(interface.into_iter()),
            TranslatedItem::TyInv { modl } => Box::new(std::iter::once(modl)),
        }
    }
}
