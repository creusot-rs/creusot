use crate::{
    contracts_items::{is_spec, is_trusted},
    ctx::{HasTyCtxt, ItemType, TranslatedItem, TranslationCtx},
    naming::ModulePath,
    util::{impl_subject, path_of_span},
};
use creusot_args::options::SpanMode;
use indexmap::IndexMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use std::{
    cell::{Cell, RefCell},
    ops::{Deref, DerefMut},
    path::PathBuf,
};
use why3::declaration::{Attribute, Decl, Meta, MetaArg, MetaIdent};

pub(crate) mod clone_map;
pub(crate) mod closures;
pub(crate) mod dependency;
pub(crate) mod logic;
pub(crate) mod namespace;
pub(crate) mod optimization;
pub(crate) mod program;
pub(crate) mod projections;
pub(crate) mod signature;
pub(crate) mod resolve;
pub(crate) mod term;
pub(crate) mod traits;
pub(crate) mod ty;
pub(crate) mod ty_inv;
pub(crate) mod wto;

/// Stores the translation of Rust items to why3.
pub struct Why3Generator<'tcx> {
    pub ctx: TranslationCtx<'tcx>,
    /// The set of namespaces that appears in the current function.
    ///
    /// It is reset at the start of each function.
    namespaces: RefCell<IndexMap<DefId, why3::Ident>>,
    /// `true` if we need to generate the namespace type for the current module.
    used_namespaces: Cell<bool>,
    pub functions: Vec<TranslatedItem>,
}

impl<'tcx> Deref for Why3Generator<'tcx> {
    type Target = TranslationCtx<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl DerefMut for Why3Generator<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

impl<'tcx> Why3Generator<'tcx> {
    pub fn new(ctx: TranslationCtx<'tcx>) -> Self {
        Why3Generator {
            ctx,
            functions: Default::default(),
            namespaces: Default::default(),
            used_namespaces: Cell::new(false),
        }
    }

    /// Translate `def_id` to a why3 module, and stores it internally.
    pub(crate) fn translate(&mut self, def_id: DefId) {
        debug!("translating {:?}", def_id);

        let translated_item = match self.item_type(def_id) {
            ItemType::Impl if self.tcx.impl_trait_ref(def_id).is_some() => {
                let modls = traits::lower_impl(self, def_id);
                TranslatedItem::Impl { modls }
            }
            ItemType::Logic { .. } => {
                let proof_modl = logic::translate_logic(self, def_id);
                TranslatedItem::Logic { proof_modl }
            }
            ItemType::Program => {
                let modl = program::translate_function(self, def_id);
                TranslatedItem::Program { modl }
            }
            ItemType::Field | ItemType::Variant => unreachable!(),
            ItemType::Unsupported(dk) => self.crash_and_error(
                self.tcx.def_span(def_id),
                format!("unsupported definition kind {:?} {:?}", def_id, dk),
            ),
            ItemType::Closure
            | ItemType::Trait
            | ItemType::Type
            | ItemType::AssocTy
            | ItemType::Impl
            | ItemType::Constant => return,
        };
        self.functions.push(translated_item);
    }

    /// Get the name of the namespace.
    ///
    /// This also:
    /// - Caches the generated name for future uses
    /// - Allow all the names defined in the current function to be later retrieved, in
    ///   order to generate the namespace type.
    pub(crate) fn get_namespace_constructor(&self, namespace_fun: DefId) -> why3::Ident {
        self.used_namespaces.set(true);
        *self.namespaces.borrow_mut().entry(namespace_fun).or_insert_with(|| {
            let name = self.ctx.item_name(namespace_fun);
            why3::Ident::fresh_local(format!("Namespace_{name}"))
        })
    }

    /// Get a why3 attribute corresponding to this span.
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
            let parent_id = key.parent?; // The last segment is CrateRoot. Skip it.

            if key.disambiguated_data.data == rustc_hir::definitions::DefPathData::Impl {
                return Some(display_impl_subject(tcx, id));
            }
            id.index = parent_id;
        }
    }

    pub(crate) fn module_path(&self, def_id: DefId) -> ModulePath {
        ModulePath::new(self.tcx, def_id)
    }
}

impl<'tcx> HasTyCtxt<'tcx> for Why3Generator<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}

fn display_impl_subject(tcx: TyCtxt, id: DefId) -> String {
    match impl_subject(tcx, id) {
        Ok(trait_ref) => trait_ref.to_string(),
        Err(ty) => ty.to_string(),
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

pub(crate) fn common_meta_decls() -> impl Iterator<Item = Decl> {
    [
        Decl::Meta(Meta {
            name: MetaIdent("compute_max_steps".into()),
            args: [MetaArg::Integer(1_000_000)].into(),
        }),
        Decl::Meta(Meta {
            name: MetaIdent("select_lsinst".into()),
            args: [MetaArg::String("all".into())].into(),
        }),
    ]
    .into_iter()
}
