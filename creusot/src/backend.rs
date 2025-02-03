use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::{RealFileName, Span};

use crate::{
    contracts_items::{is_resolve_function, is_spec, is_trusted},
    ctx::{ItemType, TranslatedItem, TranslationCtx},
    error::CannotFetchThir,
    naming::ModulePath,
    options::SpanMode,
    run_why3::SpanMap,
};
use std::ops::{Deref, DerefMut};

pub(crate) use clone_map::*;

pub(crate) mod clone_map;
pub(crate) mod dependency;
pub(crate) mod logic;
pub(crate) mod optimization;
pub(crate) mod place;
pub(crate) mod program;
pub(crate) mod signature;
pub(crate) mod structural_resolve;
pub(crate) mod term;
pub(crate) mod traits;
pub(crate) mod ty;
pub(crate) mod ty_inv;
pub(crate) mod wto;

pub struct Why3Generator<'tcx> {
    ctx: TranslationCtx<'tcx>,
    functions: Vec<TranslatedItem>,
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
        Why3Generator { ctx, functions: Default::default(), span_map: Default::default() }
    }

    pub(crate) fn translate(&mut self, def_id: DefId) -> Result<(), CannotFetchThir> {
        debug!("translating {:?}", def_id);

        // eprintln!("{:?}", self.param_env(def_id));

        match self.item_type(def_id) {
            ItemType::Impl if self.tcx.impl_trait_ref(def_id).is_some() => {
                let modls = traits::lower_impl(self, def_id);
                self.functions.push(TranslatedItem::Impl { modls });
            }
            ItemType::Predicate { .. } if is_resolve_function(self.tcx, def_id) => {
                self.functions.push(TranslatedItem::Logic { proof_modl: None });
            }
            ItemType::Logic { .. } | ItemType::Predicate { .. } => {
                let proof_modl = logic::translate_logic_or_predicate(self, def_id)?;
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
        Ok(())
    }

    pub(crate) fn modules(&mut self) -> impl Iterator<Item = TranslatedItem> + '_ {
        self.functions.drain(..)
    }

    fn is_logical(&self, item: DefId) -> bool {
        matches!(self.item_type(item), ItemType::Logic { .. } | ItemType::Predicate { .. })
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
                let diff = pathdiff::diff_paths(&path, &base)?;
                diff.to_string_lossy().into_owned()
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

pub fn is_trusted_function(tcx: TyCtxt, mut def_id: DefId) -> bool {
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
