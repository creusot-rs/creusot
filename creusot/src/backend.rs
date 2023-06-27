use indexmap::{IndexMap, IndexSet};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{GenericParamDef, GenericParamDefKind, TyCtxt};
use rustc_span::DUMMY_SP;
use why3::declaration::{Decl, TyDecl};

use crate::{
    ctx::{TranslatedItem, TranslationCtx},
    util::{self, ItemType},
};
use std::ops::{Deref, DerefMut};

pub(crate) use clone_map::*;

use self::{dependency::Dependency, ty_inv::TyInvKind};

pub(crate) mod clone_map;
pub(crate) mod constant;
pub(crate) mod dependency;
pub(crate) mod interface;
pub(crate) mod logic;
pub(crate) mod optimization;
pub(crate) mod place;
pub(crate) mod program;
pub(crate) mod signature;
pub(crate) mod term;
pub(crate) mod traits;
pub(crate) mod ty;
pub(crate) mod ty_inv;

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) enum TransId {
    Item(DefId),
    TyInv(TyInvKind),
}

impl From<DefId> for TransId {
    fn from(def_id: DefId) -> Self {
        TransId::Item(def_id)
    }
}

pub struct Why3Generator<'tcx> {
    ctx: TranslationCtx<'tcx>,
    dependencies: IndexMap<TransId, CloneSummary<'tcx>>,
    functions: IndexMap<TransId, TranslatedItem>,
    translated_items: IndexSet<TransId>,
    in_translation: Vec<IndexSet<TransId>>,
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
    fn safe_cycle(&self, trans_id: TransId) -> bool {
        self.in_translation.last().map(|l| l.contains(&trans_id)).unwrap_or_default()
    }

    pub(crate) fn translate(&mut self, def_id: DefId) {
        let tid = def_id.into();
        if self.translated_items.contains(&tid) || self.safe_cycle(tid) {
            return;
        }
        debug!("translating {:?}", def_id);

        // eprintln!("{:?}", self.param_env(def_id));

        match util::item_type(self.tcx, def_id) {
            ItemType::Trait => {
                self.start(def_id);
                let tr = self.translate_trait(def_id);
                self.dependencies.insert(tid, CloneSummary::new());
                self.functions.insert(tid, tr);
                self.finish(def_id);
            }
            ItemType::Impl => {
                if self.tcx.impl_trait_ref(def_id).is_some() {
                    self.start(def_id);
                    let impl_ = traits::lower_impl(self, def_id);

                    self.dependencies.insert(tid, CloneSummary::new());
                    self.functions.insert(tid, TranslatedItem::Impl { modl: impl_ });
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
                self.dependencies.insert(tid, dependencies);
                self.functions.insert(tid, TranslatedItem::AssocTy { modl });
            }
            ItemType::Constant => {
                self.start(def_id);
                let (constant, dependencies) = self.translate_constant(def_id);
                self.finish(def_id);
                self.dependencies.insert(tid, dependencies);
                self.functions.insert(tid, constant);
            }
            ItemType::Type => {
                let bg = self.binding_group(def_id).clone();

                self.start_group(bg.clone());

                let modl = ty::translate_tydecl(self, &bg);

                for d in &bg {
                    self.finish(*d);
                }

                let repr = self.representative_type(def_id).into();
                if let Some(modl) = modl {
                    self.functions
                        .insert(repr, TranslatedItem::Type { modl, accessors: Default::default() });
                }
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
                self.dependencies.insert(def_id.into(), deps);

                TranslatedItem::Logic { stub, interface, modl, proof_modl, has_axioms }
            }
            ItemType::Closure => {
                let (ty_modl, modl) = program::translate_closure(self, def_id);
                self.dependencies.insert(def_id.into(), deps);

                TranslatedItem::Closure { interface: vec![ty_modl, interface], modl }
            }
            ItemType::Program => {
                debug!("translating {def_id:?} as program");

                self.dependencies.insert(def_id.into(), deps);
                let modl = program::translate_function(self, def_id);
                TranslatedItem::Program { interface, modl }
            }
            _ => unreachable!(),
        };

        self.functions.insert(def_id.into(), translated);
    }

    pub(crate) fn translate_accessor(&mut self, field_id: DefId) {
        if !self.translated_items.insert(field_id.into()) {
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
        let repr_id: TransId = self.representative_type(adt_did).into();
        if let TranslatedItem::Type { ref mut accessors, .. } = &mut self.functions[&repr_id] {
            accessors.entry(variant_did).or_default().insert(field_id, accessor);
        };
        // self.types[&repr_id].accessors;
    }

    pub(crate) fn translate_tyinv(&mut self, inv_kind: TyInvKind) {
        let tid = TransId::TyInv(inv_kind);
        if self.dependencies.contains_key(&tid) {
            return;
        }

        if let TyInvKind::Adt(adt_did) = inv_kind {
            self.translate(adt_did);
        }

        let (modl, deps) = ty_inv::build_inv_module(self, inv_kind);
        self.dependencies.insert(tid, deps);
        self.functions.insert(tid, TranslatedItem::TyInv { modl });
    }

    pub(crate) fn item(&self, def_id: DefId) -> Option<&TranslatedItem> {
        let tid: TransId = if matches!(util::item_type(***self, def_id), ItemType::Type) {
            self.representative_type(def_id)
        } else {
            def_id
        }
        .into();
        self.functions.get(&tid)
    }

    pub(crate) fn modules(self) -> impl Iterator<Item = (TransId, TranslatedItem)> + 'tcx {
        self.functions.into_iter()
    }

    pub(crate) fn start_group(&mut self, ids: IndexSet<DefId>) {
        assert!(!ids.is_empty());
        let ids = ids.into_iter().map(Into::into).collect();
        if self.in_translation.iter().rev().any(|s| !s.is_disjoint(&ids)) {
            let span = if let TransId::Item(def_id) = ids.first().unwrap() {
                self.def_span(def_id)
            } else {
                DUMMY_SP
            };

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
        let tid = def_id.into();
        if !self.in_translation.last_mut().unwrap().remove(&tid) {
            self.crash_and_error(
                self.def_span(def_id),
                &format!("{:?} is not in translation", def_id),
            );
        }

        if self.in_translation.last().unwrap().is_empty() {
            self.in_translation.pop();
        }

        self.translated_items.insert(tid);
    }

    pub(crate) fn dependencies(&self, key: Dependency<'tcx>) -> Option<&CloneSummary<'tcx>> {
        let tid = match key {
            Dependency::TyInv(ty) => TransId::TyInv(TyInvKind::from_ty(ty)),
            _ => key.did().map(|(def_id, _)| TransId::Item(def_id))?,
        };
        self.dependencies.get(&tid)
    }
}

// Closures inherit the generic parameters of the original function they were defined in, but
// add 3 'ghost' generics tracking metadata about the closure. We choose to erase those parameters,
// as they contain a function type along with other irrelevant details (for us).
pub(crate) fn closure_generic_decls(
    tcx: TyCtxt,
    mut def_id: DefId,
) -> impl Iterator<Item = Decl> + '_ {
    loop {
        if tcx.is_closure(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            break;
        }
    }

    all_generic_decls_for(tcx, def_id)
}

pub(crate) fn all_generic_decls_for(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = Decl> + '_ {
    let generics = tcx.generics_of(def_id);

    generic_decls((0..generics.count()).map(move |i| generics.param_at(i, tcx)))
}

pub(crate) fn own_generic_decls_for(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = Decl> + '_ {
    let generics = tcx.generics_of(def_id);
    generic_decls(generics.params.iter())
}

fn generic_decls<'tcx, I: Iterator<Item = &'tcx GenericParamDef> + 'tcx>(
    it: I,
) -> impl Iterator<Item = Decl> + 'tcx {
    it.filter_map(|param| {
        if let GenericParamDefKind::Type { .. } = param.kind {
            Some(Decl::TyDecl(TyDecl::Opaque {
                ty_name: (&*param.name.as_str().to_lowercase()).into(),
                ty_params: vec![],
            }))
        } else {
            None
        }
    })
}
