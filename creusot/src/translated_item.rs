use indexmap::IndexMap;
use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Module};

pub enum TranslatedItem {
    Logic {
        // A module which contains the function body (and contract) but uses the actual bodies of all called functions
        proof_modl: Option<Module>,
    },
    Closure {
        ty_modl: Module,
        modl: Option<Module>,
    },
    Program {
        modl: Option<Module>,
    },
    Trait {},
    Impl {
        modl: Module, // Refinement of traits,
    },
    AssocTy {},
    Constant {},
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
    pub(crate) fn modules(self) -> Box<dyn Iterator<Item = Module>> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Logic { proof_modl, .. } => Box::new(proof_modl.into_iter()),
            Program { modl, .. } => Box::new(modl.into_iter()),
            Trait { .. } => Box::new(iter::empty()),
            Impl { modl, .. } => Box::new(iter::once(modl)),
            AssocTy { .. } => Box::new(iter::empty()),
            Constant { .. } => Box::new(iter::empty()),
            Type { mut modl, accessors, .. } => {
                modl[0].decls.extend(accessors.values().flat_map(|v| v.values()).cloned());

                Box::new(modl.into_iter())
            }
            Closure { ty_modl, modl, .. } => Box::new(iter::once(ty_modl).chain(modl.into_iter())),
            TyInv { .. } => Box::new(iter::empty()),
        }
    }
}
