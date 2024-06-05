use indexmap::{IndexMap, IndexSet};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{AliasTy, GenericParamDef, GenericParamDefKind, TyCtxt};
use rustc_span::{RealFileName, Span, DUMMY_SP};
use why3::declaration::{Decl, TyDecl};

use crate::{
    backend::interface::interface_for,
    ctx::{TranslatedItem, TranslationCtx},
    translation::pearlite::Term,
    util::{self, ItemType},
};
use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use crate::{options::SpanMode, run_why3::SpanMap};
pub(crate) use clone_map::*;
use why3::Exp;

use self::{
    dependency::{Dependency, ExtendedId},
    ty_inv::TyInvKind,
};

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
mod wto;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum TransId {
    Item(DefId),
    TyInv(TyInvKind),
    Hacked(ExtendedId, DefId),
}

impl From<DefId> for TransId {
    fn from(def_id: DefId) -> Self {
        TransId::Item(def_id)
    }
}

pub struct Why3Generator<'tcx> {
    ctx: TranslationCtx<'tcx>,
    dependencies: IndexMap<TransId, CloneSummary<'tcx>>,
    projections_in_ty: HashMap<DefId, Vec<AliasTy<'tcx>>>,
    functions: IndexMap<TransId, TranslatedItem>,
    translated_items: IndexSet<TransId>,
    in_translation: Vec<IndexSet<TransId>>,
    pub(crate) span_map: SpanMap,
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
            projections_in_ty: Default::default(),
            functions: Default::default(),
            translated_items: Default::default(),
            in_translation: Default::default(),
            span_map: Default::default(),
        }
    }

    fn term(&mut self, id: impl Into<TransId>) -> Option<&Term<'tcx>> {
        match id.into() {
            TransId::Item(id) => self.ctx.term(id),
            // For the moment at least
            TransId::TyInv(_) => unreachable!(),
            TransId::Hacked(h, id) => {
                let c = self.ctx.closure_contract(id);
                match h {
                    ExtendedId::PostconditionOnce => Some(&c.postcond_once.as_ref()?.1),
                    ExtendedId::PostconditionMut => Some(&c.postcond_mut.as_ref()?.1),
                    ExtendedId::Postcondition => Some(&c.postcond.as_ref()?.1),
                    ExtendedId::Precondition => Some(&c.precond.1),
                    ExtendedId::Unnest => Some(&c.unnest.as_ref()?.1),
                    ExtendedId::Resolve => Some(&c.resolve.1),
                    ExtendedId::Accessor(ix) => Some(&c.accessors[ix as usize].1),
                }
            }
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
            ItemType::Logic { .. }
            | ItemType::Predicate { .. }
            | ItemType::Program
            | ItemType::Closure => {
                self.start(def_id);
                self.translate_function(def_id);
                self.finish(def_id);
            }
            ItemType::AssocTy => {
                self.start(def_id);
                let (_, dependencies) = self.translate_assoc_ty(def_id);
                self.finish(def_id);
                self.dependencies.insert(tid, dependencies);
                self.functions.insert(tid, TranslatedItem::AssocTy {});
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
            ItemType::Field => unreachable!(),
            ItemType::Variant => {
                self.translate(self.ctx.parent(def_id));
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

        let translated = match util::item_type(self.tcx, def_id) {
            ItemType::Logic { .. } | ItemType::Predicate { .. } => {
                debug!("translating {:?} as logical", def_id);
                let (proof_modl, deps) = logic::translate_logic_or_predicate(self, def_id);
                self.dependencies.insert(def_id.into(), deps);

                TranslatedItem::Logic { proof_modl }
            }
            ItemType::Closure => {
                let (deps, ty_modl, modl) = program::translate_closure(self, def_id);
                self.dependencies.insert(def_id.into(), deps);

                TranslatedItem::Closure { ty_modl, modl }
            }
            ItemType::Program => {
                debug!("translating {def_id:?} as program");
                let (_, modl) = program::translate_function(self, def_id);
                let deps = interface_for(self, def_id);
                self.dependencies.insert(def_id.into(), deps);
                TranslatedItem::Program { modl }
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

        let deps = ty_inv::build_inv_module(self, inv_kind);
        self.dependencies.insert(tid, deps);
        self.functions.insert(tid, TranslatedItem::TyInv {});
    }

    // pub(crate) fn item(&self, def_id: DefId) -> Option<&TranslatedItem> {
    //     let tid: TransId = if matches!(util::item_type(***self, def_id), ItemType::Type) {
    //         self.representative_type(def_id)
    //     } else {
    //         def_id
    //     }
    //     .into();
    //     self.functions.get(&tid)
    // }

    pub(crate) fn modules<'a>(
        &'a mut self,
    ) -> impl Iterator<Item = (TransId, TranslatedItem)> + 'a {
        self.functions.drain(..)
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
        let tid = key.to_trans_id()?;
        self.dependencies.get(&tid)
    }

    pub(crate) fn projections_in_ty(&mut self, item: DefId) -> &[AliasTy<'tcx>] {
        if self.projections_in_ty.get(&item).is_none() {
            let res = self.get_projections_in_ty(item);
            self.projections_in_ty.insert(item, res);
        };

        &self.projections_in_ty[&item]
    }

    fn is_logical(&self, item: DefId) -> bool {
        matches!(
            util::item_type(self.tcx, item),
            ItemType::Logic { .. } | ItemType::Predicate { .. }
        )
    }

    fn is_accessor(&self, item: TransId) -> bool {
        match item {
            TransId::Hacked(ExtendedId::Accessor(_), _) => true,
            TransId::Item(id) => self.def_kind(id) == DefKind::Field,
            _ => false,
        }
    }

    pub(crate) fn span_attr(&mut self, span: Span) -> Option<why3::declaration::Attribute> {
        if span.is_dummy() {
            return None;
        }
        if let Some(span) = self.span_map.encode_span(&self.ctx.opts, span) {
            return Some(span);
        };
        let lo = self.sess.source_map().lookup_char_pos(span.lo());
        let hi = self.sess.source_map().lookup_char_pos(span.hi());

        let rustc_span::FileName::Real(path) = &lo.file.name else { return None };

        // If we ask for relative paths and the paths comes from the standard library, then we prefer returning
        // None, since the relative path of the stdlib is not stable.
        let path = match (&self.opts.span_mode, path) {
            (SpanMode::Relative(_), RealFileName::Remapped { .. }) => return None,
            _ => path.local_path_if_available(),
        };

        let to_absolute = |path: &std::path::Path| -> std::path::PathBuf {
            if path.is_relative() {
                let mut buf = std::env::current_dir().unwrap();
                buf.push(path);
                buf
            } else {
                path.to_owned()
            }
        };

        let filename = match &self.opts.span_mode {
            SpanMode::Absolute => to_absolute(path).to_string_lossy().into_owned(),
            SpanMode::Relative(base) => {
                let path = to_absolute(path);
                let base = to_absolute(base);
                // Why3 treats the spans as relative to the session, not the source file,
                // and the session is in a subdirectory next to the coma file, so we need
                // to add an extra ".."
                let p = std::path::PathBuf::from("..");
                let diff = pathdiff::diff_paths(&path, &base)?;
                p.join(diff).to_string_lossy().into_owned()
            }
            SpanMode::Off => return None,
        };

        Some(why3::declaration::Attribute::Span(
            filename,
            lo.line,
            lo.col_display,
            hi.line,
            hi.col_display,
        ))
    }

    pub(crate) fn attach_span(&mut self, span: Span, exp: Exp) -> Exp {
        if let Some(attr) = self.span_attr(span) {
            Exp::Attr(attr, Box::new(exp))
        } else {
            exp
        }
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
        if tcx.is_closure_like(def_id) {
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
    generic_decls(generics.own_params.iter())
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
