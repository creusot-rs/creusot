use std::{collections::HashMap, ops::Deref};

pub use crate::clone_map::*;
use crate::{
    creusot_items::{self, CreusotItems},
    error::CreusotResult,
    metadata::{BinaryMetadata, Metadata},
    options::{Options, SpanMode},
    translation::{
        external,
        external::{extract_extern_specs_from_item, ExternSpec},
        interface::interface_for,
        specification,
        specification::{typing::Term, ContractClauses},
        ty,
        ty::translate_tydecl,
    },
    util,
    util::item_type,
};
use creusot_rustc::{
    data_structures::captures::Captures,
    errors::{DiagnosticBuilder, DiagnosticId},
    hir::{
        def::DefKind,
        def_id::{DefId, LocalDefId},
    },
    middle::ty::{subst::InternalSubsts, ParamEnv, TyCtxt},
    span::{Span, Symbol, DUMMY_SP},
};
use indexmap::{IndexMap, IndexSet};
pub use util::{item_name, module_name, ItemType};
use why3::{declaration::Module, exp::Exp};

pub use crate::translated_item::*;

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub translated_items: IndexSet<DefId>,
    ty_binding_groups: HashMap<DefId, DefId>, // maps type ids to their 'representative type'
    functions: IndexMap<DefId, TranslatedItem>,
    dependencies: IndexMap<DefId, CloneSummary<'tcx>>,
    terms: IndexMap<DefId, Term<'tcx>>,
    pub externs: Metadata<'tcx>,
    pub(crate) opts: &'sess Options,
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
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: &'sess Options) -> Self {
        let creusot_items = creusot_items::local_creusot_items(tcx);

        Self {
            tcx,
            translated_items: Default::default(),
            functions: Default::default(),
            dependencies: Default::default(),
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
                self.dependencies.insert(def_id, dependencies);
                self.translated_items.insert(def_id);
                self.functions.insert(def_id, TranslatedItem::AssocTy { modl });
            }
            ItemType::Constant => {
                let (modl, dependencies) = self.translate_constant(def_id);
                self.dependencies.insert(def_id, dependencies);
                self.translated_items.insert(def_id);
                self.functions.insert(def_id, TranslatedItem::Constant { modl });
            }
            ItemType::Type => {
                translate_tydecl(self, DUMMY_SP, def_id);
            }
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
            self.dependencies.insert(def_id, deps.summary());
            TranslatedItem::Logic { interface, modl, proof_modl, has_axioms }
        } else if !def_id.is_local() {
            debug!("translating {:?} as extern", def_id);

            let (body, extern_deps) = external::extern_module(self, def_id);

            if let Some(deps) = extern_deps {
                self.dependencies.insert(def_id, deps);
            }
            TranslatedItem::Extern { interface, body }
        } else {
            debug!("translating {def_id:?} as program");

            self.dependencies.insert(def_id, deps.summary());
            let modl = crate::translation::translate_function(self, def_id);
            TranslatedItem::Program { interface, modl, has_axioms: self.tcx.is_closure(def_id) }
        };

        self.functions.insert(def_id, translated);
    }

    pub fn translate_accessor(&mut self, field_id: DefId) {
        use creusot_rustc::middle::ty::DefIdTree;

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
        let repr_id = self.ty_binding_groups[&adt_did];
        if let TranslatedItem::Type { ref mut accessors, .. } = &mut self.functions[&repr_id] {
            accessors.entry(variant_did).or_default().insert(field_id, accessor);
        }
        // self.types[&repr_id].accessors;
    }

    pub fn term(&mut self, def_id: DefId) -> Option<&Term<'tcx>> {
        if !def_id.is_local() {
            return self.externs.term(def_id);
        }

        if util::has_body(self, def_id) {
            let t = self.terms.entry(def_id).or_insert_with(|| {
                let term = specification::typing::typecheck(self.tcx, def_id.expect_local())
                    .unwrap_or_else(|e| e.emit(self.tcx.sess));
                term
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

    pub fn add_binding_group(&mut self, def_ids: &IndexSet<DefId>) {
        let repr = *def_ids.first().unwrap();
        for i in def_ids {
            self.ty_binding_groups.insert(*i, repr);
        }
    }

    pub fn add_type(&mut self, def_id: DefId, modl: Module) {
        let repr = self.representative_type(def_id);
        self.functions.insert(repr, TranslatedItem::Type { modl, accessors: Default::default() });
    }

    pub fn add_trait(&mut self, def_id: DefId, laws: Vec<DefId>) {
        self.dependencies.insert(def_id, CloneSummary::new());
        self.functions.insert(def_id, TranslatedItem::Trait { laws });
    }

    pub fn add_impl(&mut self, def_id: DefId, laws: Vec<DefId>, modl: Module) {
        self.dependencies.insert(def_id, CloneSummary::new());
        self.functions.insert(def_id, TranslatedItem::Impl { modl, laws });
    }

    pub fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        self.dependencies.get(&def_id).or_else(|| {
            self.item(def_id).and_then(|f| f.external_dependencies(&self.externs, def_id))
        })
    }

    pub fn item(&self, def_id: DefId) -> Option<&TranslatedItem> {
        let def_id = self.ty_binding_groups.get(&def_id).unwrap_or(&def_id);
        self.functions.get(def_id)
    }

    // Get the id of the type which represents a binding groups
    // Panics a type hasn't yet been translated
    pub fn representative_type(&self, def_id: DefId) -> DefId {
        self.ty_binding_groups[&def_id]
    }

    // TODO Make private
    pub(crate) fn extern_spec(&self, def_id: DefId) -> Option<&ExternSpec<'tcx>> {
        self.extern_specs.get(&def_id).or_else(|| self.externs.extern_spec(def_id))
    }

    pub fn should_export(&self) -> bool {
        self.opts.export_metadata
    }

    pub fn should_compile(&self) -> bool {
        self.opts.should_output
    }

    pub fn modules(self) -> impl Iterator<Item = (DefId, TranslatedItem)> + Captures<'tcx> {
        self.functions.into_iter()
    }

    pub(crate) fn metadata(&self) -> BinaryMetadata<'tcx> {
        BinaryMetadata::from_parts(
            self.tcx,
            &self.functions,
            &self.dependencies,
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
        let (id, subst) = crate::specification::inherited_extern_spec(self, def_id)
            .unwrap_or_else(|| (def_id, InternalSubsts::identity_for_item(self.tcx, def_id)));
        if let Some(es) = self.extern_spec(id) {
            let mut additional_predicates = Vec::new();
            additional_predicates.extend(es.predicates_for(self.tcx, subst));
            additional_predicates.extend(self.tcx.param_env(def_id).caller_bounds());
            ParamEnv::new(
                self.mk_predicates(additional_predicates.into_iter()),
                creusot_rustc::infer::traits::Reveal::UserFacing,
                creusot_rustc::hir::Constness::NotConst,
            )
        } else {
            self.tcx.param_env(def_id)
        }
    }

    pub fn span_attr(&self, span: Span) -> Option<why3::declaration::Attribute> {
        let lo = self.sess.source_map().lookup_char_pos(span.lo());
        let hi = self.sess.source_map().lookup_char_pos(span.hi());

        let filename = match self.opts.span_mode {
            SpanMode::Absolute if lo.file.name.is_real() => {
                if let creusot_rustc::span::FileName::Real(path) = &lo.file.name {
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
            SpanMode::Relative => {
                // Should really be relative to the source file the location is in
                format!("../{}", self.sess.source_map().filename_for_diagnostics(&lo.file.name))
            }
            _ => return None,
        };

        Some(why3::declaration::Attribute::Span(
            filename,
            lo.line,
            lo.col_display,
            hi.line,
            hi.col_display,
        ))
    }

    pub fn attach_span(&self, span: Span, exp: Exp) -> Exp {
        if let SpanMode::Off = self.opts.span_mode {
            exp
        } else {
            Exp::Attr(self.span_attr(span).unwrap(), box exp)
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
        // let additional_predicates = creusot_rustc::middle::ty::GenericPredicates { parent: None, predicates: additional_predicates };

        ctx.extern_specs.insert(
            def_id,
            ExternSpec {
                contract: ContractClauses::new(),
                subst: InternalSubsts::identity_for_item(ctx.tcx, def_id),
                arg_subst: Vec::new(),
                additional_predicates,
            },
        );
    }

    Ok(())
}
