use std::collections::HashMap;
use std::ops::Deref;

pub use crate::clone_map::*;
use crate::creusot_items::{self, CreusotItems};
use crate::error::CreusotResult;
use crate::metadata::{BinaryMetadata, Metadata};
use crate::options::SpanMode;
use crate::translation::external::{extract_extern_specs_from_item, ExternSpec};
use crate::translation::interface::interface_for;
use crate::translation::specification::typing::Term;
use crate::translation::specification::PreContract;
use crate::translation::ty;
use crate::translation::{external, specification};
use crate::util::{closure_owner, item_type};
use crate::{options::Options, util};
use indexmap::{IndexMap, IndexSet};
use rustc_data_structures::captures::Captures;
use rustc_errors::{DiagnosticBuilder, DiagnosticId};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::subst::InternalSubsts;
use rustc_middle::ty::{ParamEnv, TyCtxt};
use rustc_span::{Span, Symbol, DUMMY_SP};
pub use util::{item_name, module_name, ItemType};
use why3::declaration::{Module, TyDecl};
use why3::exp::Exp;

pub use crate::translated_item::*;

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub translated_items: IndexSet<DefId>,
    pub types: IndexMap<DefId, TypeDeclaration>,
    ty_binding_groups: HashMap<DefId, DefId>, // maps type ids to their 'representative type'
    functions: IndexMap<DefId, TranslatedItem<'tcx>>,
    terms: IndexMap<DefId, Term<'tcx>>,
    pub externs: Metadata<'tcx>,
    pub opts: &'sess Options,
    creusot_items: CreusotItems,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    extern_spec_items: HashMap<LocalDefId, DefId>,
}

impl<'tcx> Deref for TranslationCtx<'_, 'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

impl<'tcx, 'sess> TranslationCtx<'sess, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, opts: &'sess Options) -> Self {
        let creusot_items = creusot_items::local_creusot_items(tcx);

        Self {
            tcx,
            translated_items: Default::default(),
            types: Default::default(),
            functions: Default::default(),
            externs: Metadata::new(tcx),
            terms: Default::default(),
            creusot_items,
            opts,
            ty_binding_groups: Default::default(),
            extern_specs: Default::default(),
            extern_spec_items: Default::default(),
        }
    }

    pub fn load_metadata(&mut self) {
        self.externs.load(&self.opts.extern_paths);
    }

    pub fn translate(&mut self, def_id: DefId) {
        if self.translated_items.contains(&def_id) {
            return;
        }
        debug!("translating {:?}", def_id);

        match item_type(self.tcx, def_id) {
            ItemType::Trait => self.translate_trait(def_id),
            ItemType::Impl => {
                if self.tcx.impl_trait_ref(def_id).is_some() {
                    self.translate_impl(def_id)
                }
            }

            ItemType::Logic | ItemType::Predicate | ItemType::Program => {
                self.translate_function(def_id)
            }
            ItemType::AssocTy => {
                let (modl, dependencies) = self.translate_assoc_ty(def_id);
                self.translated_items.insert(def_id);
                self.functions.insert(def_id, TranslatedItem::AssocTy { modl, dependencies });
            }
            ItemType::Constant => {
                let (modl, dependencies) = self.translate_constant(def_id);
                self.translated_items.insert(def_id);
                self.functions.insert(def_id, TranslatedItem::Constant { modl, dependencies });
            }
            ItemType::Type => unreachable!("ty"),
            ItemType::Interface => unreachable!(),
            ItemType::Closure => self.translate_function(def_id),
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

        if !self.translated_items.insert(def_id) {
            return;
        }

        if !crate::util::should_translate(self.tcx, def_id) || util::is_spec(self.tcx, def_id) {
            debug!("Skipping {:?}", def_id);
            return;
        }

        let (interface, deps) = interface_for(self, def_id);

        let translated = if util::is_logic(self.tcx, def_id) || util::is_predicate(self.tcx, def_id)
        {
            debug!("translating {:?} as logical", def_id);
            let (modl, proof_modl, has_axioms, deps) =
                crate::translation::translate_logic_or_predicate(self, def_id);
            TranslatedItem::Logic {
                interface,
                modl,
                proof_modl,
                has_axioms,
                dependencies: deps.summary(),
            }
        } else if !def_id.is_local() {
            debug!("translating {:?} as extern", def_id);

            let ext_modl = external::extern_module(self, def_id);

            TranslatedItem::Extern { interface, body: ext_modl.0, dependencies: ext_modl.1 }
        } else {
            debug!("translating {def_id:?} as program");
            let modl = crate::translation::translate_function(self, def_id);
            TranslatedItem::Program {
                interface,
                modl,
                dependencies: deps.summary(),
                has_axioms: self.tcx.is_closure(def_id),
            }
        };

        self.functions.insert(def_id, translated);
    }

    pub fn translate_accessor(&mut self, field_id: DefId) {
        use rustc_middle::ty::DefIdTree;

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

        let accessor = ty::translate_accessor(self, adt_did, variant_did, field_id);
        let repr_id = self.ty_binding_groups[&adt_did];
        self.types[&repr_id].accessors.entry(variant_did).or_default().insert(field_id, accessor);
    }

    pub fn term(&mut self, def_id: DefId) -> Option<&Term<'tcx>> {
        if !def_id.is_local() {
            return self.externs.term(def_id);
        }

        if util::has_body(self, def_id) {
            let t = self.terms.entry(def_id).or_insert_with(|| {
                let term = specification::typing::typecheck(self.tcx, def_id.expect_local())
                    .unwrap_or_else(|e| e.emit(self.tcx.sess));

                let parent = closure_owner(self.tcx, def_id);
                if let Some(_) = self
                    .extern_spec_items
                    .get(&parent.expect_local())
                    .and_then(|id| self.extern_specs.get(&id))
                {
                    let i = InternalSubsts::identity_for_item(self.tcx, def_id);
                    use rustc_middle::ty::subst::Subst;
                    term.subst(self.tcx, i)
                } else {
                    term
                }
            });
            Some(t)
        } else {
            None
        }
    }

    pub fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.tcx.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub fn fatal_error(&self, span: Span, msg: &str) -> DiagnosticBuilder<'tcx, !> {
        self.tcx.sess.struct_span_fatal_with_code(
            span,
            msg,
            DiagnosticId::Error(String::from("creusot")),
        )
    }

    pub fn error(&self, span: Span, msg: &str) {
        self.tcx.sess.span_err_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub fn warn(&self, span: Span, msg: &str) {
        self.tcx.sess.span_warn_with_code(
            span,
            msg,
            DiagnosticId::Lint {
                name: String::from("creusot"),
                has_future_breakage: false,
                is_force_warn: true,
            },
        )
    }

    pub fn add_type(&mut self, def_ids: &[DefId], decl: TyDecl) {
        self.types
            .insert(def_ids[0], TypeDeclaration { ty_decl: decl, accessors: Default::default() });
        for i in def_ids {
            self.ty_binding_groups.insert(*i, def_ids[0]);
        }
    }

    pub fn add_trait(&mut self, def_id: DefId, laws: Vec<DefId>) {
        self.functions
            .insert(def_id, TranslatedItem::Trait { laws, dependencies: CloneSummary::new() });
    }

    pub fn add_impl(&mut self, def_id: DefId, laws: Vec<DefId>, modl: Module) {
        self.functions
            .insert(def_id, TranslatedItem::Impl { modl, laws, dependencies: CloneSummary::new() });
    }

    pub fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        self.item(def_id).map(|f| f.dependencies(&self.externs))
    }

    pub fn item(&self, def_id: DefId) -> Option<&TranslatedItem<'tcx>> {
        self.functions.get(&def_id)
    }

    pub(crate) fn extern_spec(&self, def_id: DefId) -> Option<&ExternSpec<'tcx>> {
        self.extern_specs.get(&def_id).or_else(|| self.externs.extern_spec(def_id))
    }

    pub fn should_export(&self) -> bool {
        self.opts.export_metadata
    }

    pub fn should_compile(&self) -> bool {
        self.opts.should_output
    }

    pub fn modules(&self) -> impl Iterator<Item = &Module> + Captures<'tcx> {
        self.functions.values().flat_map(|m| m.modules())
    }

    pub(crate) fn metadata(&self) -> BinaryMetadata<'tcx> {
        BinaryMetadata::from_parts(
            self.tcx,
            &self.functions,
            &self.terms,
            &self.creusot_items,
            &self.extern_specs,
        )
    }

    pub fn creusot_item(&self, name: Symbol) -> Option<DefId> {
        self.creusot_items
            .symbol_to_id
            .get(&name)
            .cloned()
            .or_else(|| self.externs.creusot_item(name))
    }

    pub fn param_env(&self, def_id: DefId) -> ParamEnv<'tcx> {
        match self.extern_spec(def_id) {
            Some(es) => {
                use rustc_middle::ty;
                let mut additional_predicates = Vec::new();
                let impl_subst = ty::subst::InternalSubsts::identity_for_item(self.tcx, def_id);

                additional_predicates.extend(es.predicates_for(self.tcx, impl_subst));
                additional_predicates.extend(self.tcx.param_env(def_id).caller_bounds());
                ParamEnv::new(
                    self.mk_predicates(additional_predicates.into_iter()),
                    rustc_infer::traits::Reveal::UserFacing,
                    rustc_hir::Constness::NotConst,
                )
            }
            None => self.tcx.param_env(def_id),
        }
    }

    pub fn span_attr(&self, span: Span) -> Option<why3::declaration::Attribute> {
        let lo = self.sess.source_map().lookup_char_pos(span.lo());
        let hi = self.sess.source_map().lookup_char_pos(span.hi());

        let filename = match self.opts.span_mode {
            Some(SpanMode::Absolute) if lo.file.name.is_real() => {
                if let rustc_span::FileName::Real(path) = &lo.file.name {
                    let path = path.local_path_if_available();
                    let mut buf;
                    let path = if path.is_relative() {
                        buf = std::env::current_dir().unwrap();
                        buf.push(path);
                        buf.as_path()
                    } else {
                        path
                    };

                    path.to_string_lossy().into_owned()
                } else {
                    return None;
                }
            }
            Some(SpanMode::Relative) => {
                // Should really be relative to the source file the location is in
                format!("../{}", self.sess.source_map().filename_for_diagnostics(&lo.file.name))
            }
            _ => panic!(),
        };

        Some(why3::declaration::Attribute::Span(filename, lo.line, lo.col_display, hi.col_display))
    }

    pub fn attach_span(&self, span: Span, exp: Exp) -> Exp {
        if let Some(_) = self.opts.span_mode {
            Exp::Attr(self.span_attr(span).unwrap(), box exp)
        } else {
            exp
        }
    }
}

pub fn load_extern_specs(ctx: &mut TranslationCtx) -> CreusotResult<()> {
    let mut traits_or_impls = Vec::new();

    for def_id in ctx.tcx.hir().body_owners() {
        if crate::util::is_extern_spec(ctx.tcx, def_id.to_def_id()) {
            if let Some(container) = ctx.opt_associated_item(def_id.to_def_id()) {
                traits_or_impls.push(container.def_id)
            }

            let (i, es) = extract_extern_specs_from_item(ctx, def_id)?;
            let c = es.contract.clone();

            if ctx.extern_spec(i).is_some() {
                ctx.crash_and_error(DUMMY_SP, &format!("duplicate extern specification for {i:?}"));
            };

            let _ = ctx.extern_specs.insert(i, es);

            ctx.extern_spec_items.insert(def_id, i);

            for id in c.iter_ids() {
                ctx.term(id).unwrap();
            }
        }
    }

    // Force extern spec items to get loaded so we export them properly
    let need_to_load: Vec<_> =
        ctx.extern_specs.values().flat_map(|e| e.contract.iter_ids()).collect();

    for id in need_to_load {
        ctx.term(id);
    }

    for def_id in traits_or_impls {
        let mut additional_predicates: Vec<_> = Vec::new();
        for item in ctx.associated_items(def_id).in_definition_order() {
            additional_predicates
                .extend(ctx.extern_spec(item.def_id).unwrap().additional_predicates.clone());
        }
        // let additional_predicates = ctx.arena.alloc_slice(&additional_predicates);
        // let additional_predicates = rustc_middle::ty::GenericPredicates { parent: None, predicates: additional_predicates };

        ctx.extern_specs.insert(
            def_id,
            ExternSpec { contract: PreContract::new(), subst: Vec::new(), additional_predicates },
        );
    }

    Ok(())
}
