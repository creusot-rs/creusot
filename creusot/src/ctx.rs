use std::{collections::HashMap, ops::Deref};

pub(crate) use crate::clone_map::*;
use crate::{
    backend,
    creusot_items::{self, CreusotItems},
    error::CreusotResult,
    metadata::{BinaryMetadata, Metadata},
    options::{Options, SpanMode},
    translation::{
        self, external,
        external::{extract_extern_specs_from_item, ExternSpec},
        fmir,
        interface::interface_for,
        pearlite::{self, Term},
        specification::ContractClauses,
        traits::TraitImpl,
        ty::{self, translate_tydecl, ty_binding_group},
    },
    util::{self, item_type, PreSignature, pre_sig_of},
};
use indexmap::{IndexMap, IndexSet};
use rustc_data_structures::captures::Captures;
use rustc_errors::{DiagnosticBuilder, DiagnosticId};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_infer::traits::{Obligation, ObligationCause};
use rustc_middle::ty::{subst::InternalSubsts, ParamEnv, TyCtxt};
use rustc_span::{Span, Symbol, DUMMY_SP};
use rustc_trait_selection::traits::SelectionContext;
pub(crate) use util::{item_name, module_name, ItemType};
use why3::{declaration::Module, exp::Exp};

pub(crate) use crate::translated_item::*;

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    translated_items: IndexSet<DefId>,
    in_translation: Vec<IndexSet<DefId>>,
    representative_type: HashMap<DefId, DefId>, // maps type ids to their 'representative type'
    ty_binding_groups: HashMap<DefId, IndexSet<DefId>>,
    functions: IndexMap<DefId, TranslatedItem>,
    dependencies: IndexMap<DefId, CloneSummary<'tcx>>,
    laws: IndexMap<DefId, Vec<DefId>>,
    fmir_body: IndexMap<DefId, fmir::Body<'tcx>>,
    terms: IndexMap<DefId, Term<'tcx>>,
    pub externs: Metadata<'tcx>,
    pub(crate) opts: Options,
    creusot_items: CreusotItems,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    extern_spec_items: HashMap<LocalDefId, DefId>,
    impl_data: HashMap<DefId, TraitImpl<'tcx>>,
    sigs: HashMap<DefId, PreSignature<'tcx>>,
}

impl<'tcx> Deref for TranslationCtx<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

impl<'tcx, 'sess> TranslationCtx<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: Options) -> Self {
        let creusot_items = creusot_items::local_creusot_items(tcx);

        Self {
            tcx,
            laws: Default::default(),
            translated_items: Default::default(),
            in_translation: Default::default(),
            functions: Default::default(),
            dependencies: Default::default(),
            externs: Default::default(),
            terms: Default::default(),
            creusot_items,
            opts,
            representative_type: Default::default(),
            ty_binding_groups: Default::default(),
            extern_specs: Default::default(),
            extern_spec_items: Default::default(),
            fmir_body: Default::default(),
            impl_data: Default::default(),
            sigs: Default::default(),
        }
    }

    pub(crate) fn load_metadata(&mut self) {
        self.externs.load(self.tcx, &self.opts.extern_paths);
    }

    pub(crate) fn translate(&mut self, def_id: DefId) {
        if self.translated_items.contains(&def_id) || self.safe_cycle(def_id) {
            return;
        }
        debug!("translating {:?}", def_id);

        // eprintln!("{:?}", self.param_env(def_id));

        match item_type(self.tcx, def_id) {
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
                    let impl_ = backend::traits::lower_impl(self, def_id);

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
                translate_tydecl(self, def_id);
            }
            ItemType::Unsupported(dk) => self.crash_and_error(
                self.tcx.def_span(def_id),
                &format!("unsupported definition kind {:?} {:?}", def_id, dk),
            ),
        }
    }

    // Checks if we are allowed to recurse into
    fn safe_cycle(&self, def_id: DefId) -> bool {
        self.in_translation.last().map(|l| l.contains(&def_id)).unwrap_or_default()
    }

    pub(crate) fn trait_impl(&mut self, def_id: DefId) -> &TraitImpl<'tcx> {
        if !self.impl_data.contains_key(&def_id) {
            let trait_impl = self.translate_impl(def_id);
            self.impl_data.insert(def_id, trait_impl);
        }

        &self.impl_data[&def_id]
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

        let (interface, deps) = interface_for(self, def_id);

        let translated = if util::is_logic(self.tcx, def_id) || util::is_predicate(self.tcx, def_id)
        {
            debug!("translating {:?} as logical", def_id);
            let (stub, modl, proof_modl, has_axioms, deps) =
                crate::backend::logic::translate_logic_or_predicate(self, def_id);
            self.dependencies.insert(def_id, deps);
            TranslatedItem::Logic { stub, interface, modl, proof_modl, has_axioms }
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

    pub(crate) fn translate_accessor(&mut self, field_id: DefId) {
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
        self.translate(adt_did);

        let accessor = ty::translate_accessor(self, adt_did, variant_did, field_id);
        let repr_id = self.representative_type[&adt_did];
        if let TranslatedItem::Type { ref mut accessors, .. } = &mut self.functions[&repr_id] {
            accessors.entry(variant_did).or_default().insert(field_id, accessor);
        }
        // self.types[&repr_id].accessors;
    }

    pub(crate) fn fmir_body(&mut self, def_id: DefId) -> Option<&fmir::Body<'tcx>> {
        if util::has_body(self, def_id) && def_id.is_local() {
            if !self.fmir_body.contains_key(&def_id) {
                let fmir = translation::function::fmir(self, def_id);
                self.fmir_body.insert(def_id, fmir);
            }
            self.fmir_body.get(&def_id)
        } else {
            None
        }
    }

    pub(crate) fn term(&mut self, def_id: DefId) -> Option<&Term<'tcx>> {
        if !def_id.is_local() {
            return self.externs.term(def_id);
        }

        if util::has_body(self, def_id) {
            if !self.terms.contains_key(&def_id) {
                let mut term = pearlite::pearlite(self.tcx, def_id.expect_local())
                    .unwrap_or_else(|e| e.emit(self.tcx.sess));
                pearlite::normalize(self.tcx, self.param_env(def_id), &mut term);

                self.terms.insert(def_id, term);
            };
            self.terms.get(&def_id)
        } else {
            None
        }
    }

    pub(crate) fn sig(&mut self, def_id: DefId) -> &PreSignature<'tcx> {
        if !self.sigs.contains_key(&def_id) {
            let mut term = pre_sig_of(self, def_id);
            pearlite::normalize_sig(self.tcx, self.param_env(def_id), &mut term);

            self.sigs.insert(def_id, term);
        };
        self.sigs.get(&def_id).unwrap()
    }


    pub(crate) fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.tcx.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub(crate) fn fatal_error(&self, span: Span, msg: &str) -> DiagnosticBuilder<'tcx, !> {
        self.tcx.sess.struct_span_fatal_with_code(
            span,
            msg,
            DiagnosticId::Error(String::from("creusot")),
        )
    }

    pub(crate) fn error(&self, span: Span, msg: &str) {
        self.tcx.sess.span_err_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub(crate) fn warn(&self, span: Span, msg: &str) {
        self.tcx.sess.span_warn_with_code(
            span,
            msg,
            DiagnosticId::Lint {
                name: String::from("creusot"),
                has_future_breakage: false,
                is_force_warn: false,
            },
        )
    }

    fn add_binding_group(&mut self, def_ids: &IndexSet<DefId>) {
        let repr = *def_ids.first().unwrap();
        for i in def_ids {
            self.representative_type.insert(*i, repr);
        }
    }

    pub(crate) fn binding_group(&mut self, def_id: DefId) -> &IndexSet<DefId> {
        if !self.representative_type.contains_key(&def_id) {
            let bg = ty_binding_group(self.tcx, def_id);
            self.add_binding_group(&bg);
            self.ty_binding_groups.insert(self.representative_type(def_id), bg);
        }

        &self.ty_binding_groups[&self.representative_type(def_id)]
    }

    pub(crate) fn add_type(&mut self, def_id: DefId, modl: Vec<Module>) {
        let repr = self.representative_type(def_id);
        self.functions.insert(repr, TranslatedItem::Type { modl, accessors: Default::default() });
    }

    pub(crate) fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        self.dependencies.get(&def_id).or_else(|| {
            self.item(def_id).and_then(|f| f.external_dependencies(&self.externs, def_id))
        })
    }

    pub(crate) fn item(&self, def_id: DefId) -> Option<&TranslatedItem> {
        let def_id = self.representative_type.get(&def_id).unwrap_or(&def_id);
        self.functions.get(def_id)
    }

    // Get the id of the type which represents a binding groups
    // Panics a type hasn't yet been translated
    pub(crate) fn representative_type(&self, def_id: DefId) -> DefId {
        *self.representative_type.get(&def_id).unwrap_or_else(|| panic!("no key for {:?}", def_id))
    }

    pub(crate) fn laws(&mut self, trait_or_impl: DefId) -> &[DefId] {
        if self.laws.get(&trait_or_impl).is_none() {
            self.laws.insert(trait_or_impl, self.laws_inner(trait_or_impl));
        };

        &self.laws[&trait_or_impl]
    }

    // TODO Make private
    pub(crate) fn extern_spec(&self, def_id: DefId) -> Option<&ExternSpec<'tcx>> {
        self.extern_specs.get(&def_id).or_else(|| self.externs.extern_spec(def_id))
    }

    pub(crate) fn should_export(&self) -> bool {
        self.opts.export_metadata
    }

    pub(crate) fn should_compile(&self) -> bool {
        self.opts.should_output
    }

    pub(crate) fn modules(self) -> impl Iterator<Item = (DefId, TranslatedItem)> + Captures<'tcx> {
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

    pub(crate) fn creusot_item(&self, name: Symbol) -> Option<DefId> {
        self.creusot_items
            .symbol_to_id
            .get(&name)
            .cloned()
            .or_else(|| self.externs.creusot_item(name))
    }

    pub(crate) fn param_env(&self, def_id: DefId) -> ParamEnv<'tcx> {
        let (id, subst) = crate::specification::inherited_extern_spec(self, def_id)
            .unwrap_or_else(|| (def_id, InternalSubsts::identity_for_item(self.tcx, def_id)));
        if let Some(es) = self.extern_spec(id) {
            let mut additional_predicates = Vec::new();

            let base_env = self.tcx.param_env(def_id);
            {
                // Only add predicates which don't already hold
                use rustc_infer::infer::TyCtxtInferExt;
                let infcx = self.tcx.infer_ctxt().build();
                let mut selcx = SelectionContext::new(&infcx);
                let param_env = self.tcx.param_env(def_id);
                for pred in es.predicates_for(self.tcx, subst) {
                    let obligation_cause = ObligationCause::dummy();
                    let obligation = Obligation::new(self.tcx, obligation_cause, param_env, pred);
                    if !selcx.predicate_may_hold_fatal(&obligation) {
                        additional_predicates.push(
                            self.tcx.try_normalize_erasing_regions(base_env, pred).unwrap_or(pred),
                        )
                    }
                }
            }

            additional_predicates.extend(base_env.caller_bounds());
            ParamEnv::new(
                self.mk_predicates(additional_predicates.into_iter()),
                rustc_infer::traits::Reveal::UserFacing,
                rustc_hir::Constness::NotConst,
            )
        } else {
            self.tcx.param_env(def_id)
        }
    }

    pub(crate) fn span_attr(&self, span: Span) -> Option<why3::declaration::Attribute> {
        let lo = self.sess.source_map().lookup_char_pos(span.lo());
        let hi = self.sess.source_map().lookup_char_pos(span.hi());

        let rustc_span::FileName::Real(path) = &lo.file.name else { return None };

        let path = path.local_path_if_available();
        let mut buf;
        let path = if path.is_relative() {
            buf = std::env::current_dir().unwrap();
            buf.push(path);
            buf.as_path()
        } else {
            path
        };

        let filename = match self.opts.span_mode {
            SpanMode::Absolute => path.to_string_lossy().into_owned(),
            SpanMode::Relative => {
                // Why3 treats the spans as relative to the session not the source file??
                format!("{}", self.opts.relative_to_output(&path).to_string_lossy())
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

    pub(crate) fn attach_span(&self, span: Span, exp: Exp) -> Exp {
        if let SpanMode::Off = self.opts.span_mode {
            exp
        } else {
            Exp::Attr(self.span_attr(span).unwrap(), box exp)
        }
    }
}

pub(crate) fn load_extern_specs(ctx: &mut TranslationCtx) -> CreusotResult<()> {
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
