use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use why3::declaration::Attribute;

use crate::{
    contracts_items::{is_resolve_function, is_spec, is_trusted},
    ctx::{ItemType, TranslatedItem, TranslationCtx},
    naming::ModulePath,
    options::SpanMode,
    util::path_of_span,
};
use std::{
    ops::{Deref, DerefMut},
    path::PathBuf,
};

pub(crate) mod clone_map;
pub(crate) mod closures;
pub(crate) mod dependency;
pub(crate) mod logic;
pub(crate) mod optimization;
pub(crate) mod program;
pub(crate) mod projections;
pub(crate) mod signature;
pub(crate) mod structural_resolve;
pub(crate) mod term;
pub(crate) mod traits;
pub(crate) mod ty;
pub(crate) mod ty_inv;
pub(crate) mod wto;

pub struct Why3Generator<'tcx> {
    pub ctx: TranslationCtx<'tcx>,
    functions: Vec<TranslatedItem>,
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
        Why3Generator { ctx, functions: Default::default() }
    }

    pub(crate) fn translate(&mut self, def_id: DefId) {
        debug!("translating {:?}", def_id);

        match self.item_type(def_id) {
            ItemType::Impl if self.tcx.impl_trait_ref(def_id).is_some() => {
                let modls = traits::lower_impl(self, def_id);
                self.functions.push(TranslatedItem::Impl { modls });
            }
            ItemType::Logic { .. } if is_resolve_function(self.tcx, def_id) => {
                self.functions.push(TranslatedItem::Logic { proof_modl: None });
            }
            ItemType::Logic { .. } => {
                let proof_modl = logic::translate_logic(self, def_id);
                self.functions.push(TranslatedItem::Logic { proof_modl });
            }
            ItemType::Program => {
                let modl = program::translate_function(self, def_id);
                self.functions.push(TranslatedItem::Program { modl });
            }
            ItemType::Field | ItemType::Variant => unreachable!(),
            ItemType::Unsupported(dk) => self.crash_and_error(
                self.tcx.def_span(def_id),
                &format!("unsupported definition kind {:?} {:?}", def_id, dk),
            ),
            _ => (),
        }
    }

    pub(crate) fn modules(&mut self) -> impl Iterator<Item = TranslatedItem> + '_ {
        self.functions.drain(..)
    }

    pub(crate) fn span_attr(&self, span: Span) -> Option<Attribute> {
        let path = path_of_span(self.tcx, span, &self.opts.span_mode)?;

        let lo = self.sess.source_map().lookup_char_pos(span.lo());
        let hi = self.sess.source_map().lookup_char_pos(span.hi());

        let path: PathBuf = if path.is_relative() {
            let mut buf = std::env::current_dir().unwrap();
            buf.push(path);
            buf
        } else {
            path.into()
        };

        let filename = match &self.opts.span_mode {
            SpanMode::Absolute => path.to_string_lossy().into_owned(),
            SpanMode::Relative(base) => {
                if let Some(rustc_base) = &self.sess.opts.real_rust_source_base_dir
                    && path.starts_with(rustc_base)
                {
                    // HACK: don't produce relative paths to standard library
                    // HACK: this seems awfully specific to stdlib
                    return None;
                }

                let base = if base.is_relative() {
                    let mut buf = std::env::current_dir().unwrap();
                    buf.push(base);
                    buf
                } else {
                    base.into()
                };

                let diff = pathdiff::diff_paths(&path, &base)?;
                diff.to_string_lossy().into_owned()
            }
            SpanMode::Off => unreachable!(),
        };

        Some(Attribute::Span(filename, lo.line, lo.col_display, hi.line, hi.col_display))
    }

    pub fn display_impl_of(&self, def_id: DefId) -> Option<String> {
        let tcx = self.ctx.tcx;
        let mut id = def_id;
        loop {
            let key = tcx.def_key(id);
            let parent_id = match key.parent {
                None => return None, // The last segment is CrateRoot. Skip it.
                Some(parent_id) => parent_id,
            };
            if key.disambiguated_data.data == rustc_hir::definitions::DefPathData::Impl {
                return Some(display_impl_subject(&tcx.impl_subject(id).skip_binder()));
            }
            id.index = parent_id;
        }
    }

    pub(crate) fn module_path(&self, def_id: DefId) -> ModulePath {
        ModulePath::new(self.tcx, def_id)
    }
}

fn display_impl_subject(i: &rustc_middle::ty::ImplSubject<'_>) -> String {
    match i {
        rustc_middle::ty::ImplSubject::Trait(trait_ref) => trait_ref.to_string(),
        rustc_middle::ty::ImplSubject::Inherent(ty) => ty.to_string(),
    }
}

pub fn is_trusted_item(tcx: TyCtxt, mut def_id: DefId) -> bool {
    if is_spec(tcx, def_id) {
        return false;
    }
    if is_trusted(tcx, def_id) {
        return true;
    }
    while let Some(parent) = tcx.opt_parent(def_id) {
        if is_trusted(tcx, def_id)
            && matches!(
                tcx.def_kind(def_id),
                DefKind::Mod | DefKind::AssocFn | DefKind::Fn | DefKind::Closure
            )
        {
            return true;
        }
        def_id = parent;
    }

    false
}
