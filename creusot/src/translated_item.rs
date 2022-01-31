pub use crate::clone_map::*;
use crate::{metadata::Metadata, translation::LogicItem};
use crate::util;
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
pub use util::{item_name, module_name, ItemType};
use why3::declaration::{Decl, Module, TyDecl};

pub enum TranslatedItem<'tcx> {
    Logic(LogicItem<'tcx>),
    Program {
        interface: Module,
        modl: Module,
        dependencies: CloneSummary<'tcx>,
    },
    Trait {
        laws: Vec<DefId>,
        dependencies: CloneSummary<'tcx>, // always empty
    },
    Impl {
        laws: Vec<DefId>, // Instantiations of trait laws
        modl: Module,     // Refinement of traits,
        dependencies: CloneSummary<'tcx>,
    },
    AssocTy {
        modl: Module,
        dependencies: CloneSummary<'tcx>,
    },
    Extern {
        interface: Module,
        body: Module,
        dependencies: Result<CloneSummary<'tcx>, DefId>,
    },
}

pub struct TypeDeclaration {
    pub ty_decl: TyDecl,
    pub accessors: IndexMap<DefId, IndexMap<DefId, Vec<Decl>>>,
}

impl TypeDeclaration {
    pub fn accessors(&self) -> impl Iterator<Item = &Decl> {
        self.accessors.values().flat_map(|v| v.values().flat_map(|f| f.iter()))
    }
}

pub enum DefaultOrExtern<'tcx> {
    // dependencies is always empty.
    Default { modl: Module, dependencies: CloneSummary<'tcx> },
    Extern { modl: Module, def_id: DefId },
}

impl TranslatedItem<'tcx> {
    pub fn dependencies(&'a self, metadata: &'a Metadata<'tcx>) -> &'a CloneSummary<'tcx> {
        use TranslatedItem::*;
        match self {
            Extern { dependencies, .. } => match dependencies {
                Ok(deps) => deps,
                Err(id) => metadata.dependencies(*id).unwrap(),
            },
            _ => self.local_dependencies(),
        }
    }

    // Get the dependencies of a locally defined function
    // Panics if `self` is not local
    pub fn local_dependencies(&self) -> &CloneSummary<'tcx> {
        use TranslatedItem::*;

        match self {
            Logic(LogicItem { dependencies, .. }) => dependencies,
            Program { dependencies, .. } => dependencies,
            Trait { dependencies, .. } => dependencies,
            Impl { dependencies, .. } => dependencies,
            AssocTy { dependencies, .. } => dependencies,
            Extern { .. } => unreachable!("local_dependencies: called on a non-local item"),
        }
    }

    pub fn has_axioms(&self) -> bool {
        match self {
            TranslatedItem::Logic(LogicItem { has_axioms, .. }) => *has_axioms,
            _ => false,
        }
    }

    pub fn laws(&self) -> Option<&[DefId]> {
        match self {
            TranslatedItem::Trait { laws, .. } => Some(&laws[..]),
            TranslatedItem::Impl { laws, .. } => Some(&laws[..]),
            _ => None,
        }
    }

    pub fn modules(&'a self) -> Box<dyn Iterator<Item = &Module> + 'a> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Logic(LogicItem { interface, body, proof_obligations, .. }) => {
                box iter::once(interface).chain(iter::once(body)).chain(proof_obligations.iter())
            }
            Program { interface, modl, .. } => box iter::once(interface).chain(iter::once(modl)),
            Trait { .. } => box iter::empty(),
            Impl { modl, .. } => box iter::once(modl),
            AssocTy { modl, .. } => box iter::once(modl),
            Extern { interface, body, .. } => box iter::once(interface).chain(iter::once(body)),
        }
    }
}
