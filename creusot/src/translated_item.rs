use indexmap::IndexMap;
use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Module};

/// Module with a path to the file it is defined in.
/// We use this for modular translation (one file per module).
/// In monolithic translation, the path is left empty.
pub struct FileModule {
    pub path: crate::util::ModulePath,
    pub modl: Module,
}

pub enum TranslatedItem {
    Logic {
        /// Proof obligations emerging from the contract of a logic function
        proof_modl: Option<FileModule>,
    },
    Closure {
        /// The closure as a type
        ty_modl: FileModule,
        /// The program of the closure
        modl: Option<FileModule>,
    },
    Program {
        /// An ordinary Rust function
        modl: Option<FileModule>,
    },
    Trait {},
    Impl {
        /// Trait refinement obligations
        modl: FileModule,
    },
    AssocTy {},
    Constant {},
    Type {
        modl: Vec<FileModule>,
        accessors: IndexMap<DefId, IndexMap<DefId, Decl>>,
    },
}

impl<'a> TranslatedItem {
    pub(crate) fn modules(self) -> Box<dyn Iterator<Item = FileModule>> {
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
                modl[0].modl.decls.extend(accessors.values().flat_map(|v| v.values()).cloned());

                Box::new(modl.into_iter())
            }
            Closure { ty_modl, modl, .. } => Box::new(iter::once(ty_modl).chain(modl.into_iter())),
        }
    }
}
