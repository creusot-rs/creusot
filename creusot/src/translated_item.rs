pub use crate::clone_map::*;
use crate::{metadata::Metadata, util};
use creusot_rustc::hir::def_id::DefId;
use indexmap::IndexMap;
use rustc_middle::ty::ProjectionTy;
pub use util::{item_name, module_name, ItemType};
use why3::{
    declaration::{Decl, Module, TyDecl},
    Ident,
};

pub enum TranslatedItem<'tcx> {
    Logic {
        interface: Module,
        modl: Module,
        proof_modl: Option<Module>,
        has_axioms: bool,
    },
    Program {
        interface: Module,
        modl: Module,
        has_axioms: bool,
    },
    Trait {},
    Impl {
        modl: Module, // Refinement of traits,
    },
    AssocTy {
        modl: Module,
    },
    Extern {
        interface: Module,
        body: Module,
    },
    Constant {
        modl: Module,
    },
    // Types can not have dependencies yet, as Why3 does not yet have applicative clones
    Type {
        modl: Module,
        accessors: IndexMap<DefId, IndexMap<DefId, Decl>>,
        associated_types: IndexMap<ProjectionTy<'tcx>, Ident>,
    },
    BuiltinType,
}

pub struct TypeDeclaration {
    pub ty_decl: TyDecl,
    pub accessors: IndexMap<DefId, IndexMap<DefId, Decl>>,
}

impl TypeDeclaration {
    pub fn accessors(&self) -> impl Iterator<Item = &Decl> {
        self.accessors.values().flat_map(|v| v.values())
    }
}

impl<'tcx> TranslatedItem<'tcx> {
    pub fn external_dependencies<'a>(
        &'a self,
        metadata: &'a Metadata<'tcx>,
        id: DefId,
    ) -> Option<&'a CloneSummary<'tcx>> {
        match self {
            TranslatedItem::Extern { .. } => Some(metadata.dependencies(id).unwrap()),
            _ => None,
        }
    }

    pub fn has_axioms(&self) -> bool {
        match self {
            TranslatedItem::Logic { has_axioms, .. } => *has_axioms,
            TranslatedItem::Program { has_axioms, .. } => *has_axioms,
            _ => false,
        }
    }

    pub fn modules(self) -> Box<dyn Iterator<Item = Module>> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Logic { interface, modl, proof_modl, .. } => {
                box iter::once(interface).chain(iter::once(modl)).chain(proof_modl.into_iter())
            }
            Program { interface, modl, .. } => box iter::once(interface).chain(iter::once(modl)),
            Trait { .. } => box iter::empty(),
            Impl { modl, .. } => box iter::once(modl),
            AssocTy { modl, .. } => box iter::once(modl),
            Constant { modl, .. } => box iter::once(modl),
            Extern { interface, body, .. } => box iter::once(interface).chain(iter::once(body)),
            Type { mut modl, accessors, .. } => {
                modl.decls.extend(accessors.values().flat_map(|v| v.values()).cloned());

                box iter::once(modl)
            }
            TranslatedItem::BuiltinType => box std::iter::empty(),
        }
    }

    pub fn interface(self) -> Box<dyn Iterator<Item = Module>> {
        match self {
            TranslatedItem::Logic { interface, modl, .. } => {
                box std::iter::once(interface).chain(std::iter::once(modl))
            }
            TranslatedItem::Program { interface, .. } => box std::iter::once(interface),
            TranslatedItem::Trait { .. } => box std::iter::empty(),
            TranslatedItem::Impl { modl, .. } => box std::iter::once(modl),
            TranslatedItem::AssocTy { modl, .. } => box std::iter::once(modl),
            TranslatedItem::Extern { interface, .. } => box std::iter::once(interface),
            TranslatedItem::Constant { modl, .. } => box std::iter::once(modl),
            TranslatedItem::Type { .. } => self.modules(),
            TranslatedItem::BuiltinType => box std::iter::empty(),
        }
    }
}
