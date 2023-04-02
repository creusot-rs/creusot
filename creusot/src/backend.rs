use indexmap::{IndexMap, IndexSet};
use rustc_hir::{def::DefKind, def_id::DefId};
use why3::declaration::Module;

use crate::{
    ctx::{TranslatedItem, TranslationCtx},
    util::{self, ItemType},
};
use std::ops::{Deref, DerefMut};

use self::clone_map::CloneSummary;

pub(crate) mod clone_map;
pub(crate) mod constant;
pub(crate) mod dependency;
pub(crate) mod interface;
pub(crate) mod logic;
pub(crate) mod place;
pub(crate) mod program;
pub(crate) mod signature;
pub(crate) mod term;
pub(crate) mod traits;
pub(crate) mod ty;

pub struct Why3Generator<'tcx> {
    ctx: TranslationCtx<'tcx>,
    dependencies: IndexMap<DefId, CloneSummary<'tcx>>,
    functions: IndexMap<DefId, TranslatedItem>,
    translated_items: IndexSet<DefId>,
    in_translation: Vec<IndexSet<DefId>>,
}

impl<'tcx> Deref for Why3Generator<'tcx> {
    type Target = TranslationCtx<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl<'tcx> DerefMut for Why3Generator<'tcx> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

impl<'tcx> Why3Generator<'tcx> {
    pub fn new(ctx: TranslationCtx<'tcx>) -> Self {
        Why3Generator {
            ctx,
            dependencies: Default::default(),
            functions: Default::default(),
            translated_items: Default::default(),
            in_translation: Default::default(),
        }
    }

    // Checks if we are allowed to recurse into
    fn safe_cycle(&self, def_id: DefId) -> bool {
        self.in_translation.last().map(|l| l.contains(&def_id)).unwrap_or_default()
    }

    pub(crate) fn translate(&mut self, def_id: DefId) {
        if self.translated_items.contains(&def_id) || self.safe_cycle(def_id) {
            return;
        }
        debug!("translating {:?}", def_id);

        // eprintln!("{:?}", self.param_env(def_id));

        match util::item_type(self.tcx, def_id) {
            ItemType::Trait => {
                self.start(def_id);
                let tr = self.translate_trait(def_id);
                self.dependencies.insert(def_id, CloneSummary::new());
                self.functions.insert(def_id, tr);
                self.finish(def_id);
            }
            ItemType::Impl => {
                if self.tcx.impl_trait_ref(def_id).is_some() {
                    self.start(def_id);
                    let impl_ = traits::lower_impl(self, def_id);

                    self.dependencies.insert(def_id, CloneSummary::new());
                    self.functions.insert(def_id, TranslatedItem::Impl { modl: impl_ });
                    self.finish(def_id);
                }
            }
            ItemType::Logic | ItemType::Predicate | ItemType::Program | ItemType::Closure => {
                self.start(def_id);
                self.translate_function(def_id);
                self.finish(def_id);
            }
            ItemType::AssocTy => {
                self.start(def_id);
                let (modl, dependencies) = self.translate_assoc_ty(def_id);
                self.finish(def_id);
                self.dependencies.insert(def_id, dependencies);
                self.functions.insert(def_id, TranslatedItem::AssocTy { modl });
            }
            ItemType::Constant => {
                self.start(def_id);
                let (constant, dependencies) = self.translate_constant(def_id);
                self.finish(def_id);
                self.dependencies.insert(def_id, dependencies);
                self.functions.insert(def_id, constant);
            }
            ItemType::Type => {
                ty::translate_tydecl(self, def_id);
            }
            ItemType::Unsupported(dk) => self.crash_and_error(
                self.tcx.def_span(def_id),
                &format!("unsupported definition kind {:?} {:?}", def_id, dk),
            ),
        }
    }

    // Generic entry point for function translation
    fn translate_function(&mut self, def_id: DefId) {
        assert!(matches!(
            self.tcx.def_kind(def_id),
            DefKind::Fn | DefKind::Closure | DefKind::AssocFn
        ));

        if !crate::util::should_translate(self.tcx, def_id) || util::is_spec(self.tcx, def_id) {
            debug!("Skipping {:?}", def_id);
            return;
        }

        let (interface, deps) = interface::interface_for(self, def_id);

        let translated = match util::item_type(self.tcx, def_id) {
            ItemType::Logic | ItemType::Predicate => {
                debug!("translating {:?} as logical", def_id);
                let (stub, modl, proof_modl, has_axioms, deps) =
                    crate::backend::logic::translate_logic_or_predicate(self, def_id);
                self.dependencies.insert(def_id, deps);

                TranslatedItem::Logic { stub, interface, modl, proof_modl, has_axioms }
            }
            ItemType::Closure => {
                let (ty_modl, modl) = program::translate_closure(self, def_id);
                self.dependencies.insert(def_id, deps);

                TranslatedItem::Closure { interface: vec![ty_modl, interface], modl }
            }
            ItemType::Program => {
                debug!("translating {def_id:?} as program");

                self.dependencies.insert(def_id, deps);
                let modl = program::translate_function(self, def_id);
                TranslatedItem::Program { interface, modl }
            }
            _ => unreachable!(),
        };

        self.functions.insert(def_id, translated);
    }

    pub(crate) fn translate_accessor(&mut self, field_id: DefId) {
        if !self.translated_items.insert(field_id) {
            return;
        }

        let parent = self.tcx.parent(field_id);
        let (adt_did, variant_did) = match self.tcx.def_kind(parent) {
            DefKind::Variant => (self.tcx.parent(parent), parent),
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                (parent, self.tcx.adt_def(parent).variants()[0u32.into()].def_id)
            }
            _ => unreachable!(),
        };
        self.translate(adt_did);

        let accessor = ty::translate_accessor(self, adt_did, variant_did, field_id);
        let repr_id = self.representative_type(adt_did);
        if let TranslatedItem::Type { ref mut accessors, .. } = &mut self.functions[&repr_id] {
            accessors.entry(variant_did).or_default().insert(field_id, accessor);
        };
        // self.types[&repr_id].accessors;
    }

    pub(crate) fn add_type(&mut self, def_id: DefId, modl: Vec<Module>) {
        let repr = self.representative_type(def_id);
        self.functions.insert(repr, TranslatedItem::Type { modl, accessors: Default::default() });
    }

    pub(crate) fn item(&self, def_id: DefId) -> Option<&TranslatedItem> {
        let def_id = if matches!(util::item_type(***self, def_id), ItemType::Type) {
            self.representative_type(def_id)
        } else {
            def_id
        };
        self.functions.get(&def_id)
    }

    pub(crate) fn modules(self) -> impl Iterator<Item = (DefId, TranslatedItem)> + 'tcx {
        self.functions.into_iter()
    }

    pub(crate) fn start_group(&mut self, ids: IndexSet<DefId>) {
        assert!(!ids.is_empty());
        if self.in_translation.iter().rev().any(|s| !s.is_disjoint(&ids)) {
            let span = self.def_span(ids.first().unwrap());
            self.in_translation.push(ids);

            self.crash_and_error(
                span,
                &format!("encountered a cycle during translation: {:?}", self.in_translation),
            );
        }

        self.in_translation.push(ids);
    }

    // Mark an id as in translation.
    pub(crate) fn start(&mut self, def_id: DefId) {
        self.start_group(IndexSet::from_iter([def_id]));
    }

    // Indicate we have finished translating a given id
    pub(crate) fn finish(&mut self, def_id: DefId) {
        if !self.in_translation.last_mut().unwrap().remove(&def_id) {
            self.crash_and_error(
                self.def_span(def_id),
                &format!("{:?} is not in translation", def_id),
            );
        }

        if self.in_translation.last().unwrap().is_empty() {
            self.in_translation.pop();
        }

        self.translated_items.insert(def_id);
    }

    pub(crate) fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        self.dependencies.get(&def_id)
    }
}
