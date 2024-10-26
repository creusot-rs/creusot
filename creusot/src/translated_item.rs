use indexmap::IndexMap;
use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Module};

pub enum TranslatedItem {
    Logic {
        /// Proof obligations emerging from the contract of a logic function
        proof_modl: Option<Module>,
    },
    Closure {
        /// The closure as a type
        ty_modl: Module,
        /// The program of the closure
        modl: Option<Module>,
    },
    Program {
        /// An ordinary Rust function
        modl: Option<Module>,
    },
    Trait {},
    Impl {
        /// Trait refinement obligations
        modls: Vec<Module>,
    },
    AssocTy {},
    Constant {},
    Type {
        modl: Vec<Module>,
        accessors: IndexMap<DefId, IndexMap<DefId, Decl>>,
    },
}

impl<'a> TranslatedItem {
    pub(crate) fn modules(self) -> Box<dyn Iterator<Item = Module>> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Logic { proof_modl } => Box::new(proof_modl.into_iter()),
            Program { modl } => Box::new(modl.into_iter()),
            Trait {} => Box::new(iter::empty()),
            Impl { modls } => Box::new(modls.into_iter()),
            AssocTy {} => Box::new(iter::empty()),
            Constant {} => Box::new(iter::empty()),
            Type { mut modl, accessors, .. } => {
                modl[0].decls.extend(accessors.values().flat_map(|v| v.values()).cloned());

                Box::new(modl.into_iter())
            }
            Closure { ty_modl, modl } => Box::new(iter::once(ty_modl).chain(modl.into_iter())),
        }
    }
}
