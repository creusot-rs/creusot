use std::{collections::HashMap, ops::Deref};

pub(crate) use crate::backend::clone_map::*;
use crate::{
    backend::{ty::ty_binding_group, ty_inv},
    callbacks,
    creusot_items::{self, CreusotItems},
    error::{CrErr, CreusotResult, Error},
    metadata::{BinaryMetadata, Metadata},
    options::{Options, SpanMode},
    translation::{
        self,
        external::{extract_extern_specs_from_item, ExternSpec},
        fmir,
        pearlite::{self, Term},
        specification::{ContractClauses, PurityVisitor},
        traits::TraitImpl,
    },
    util::{self, pre_sig_of, PreSignature},
};
use indexmap::{IndexMap, IndexSet};
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_errors::{DiagnosticBuilder, DiagnosticId};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_infer::traits::{Obligation, ObligationCause};
use rustc_middle::{
    mir::{Body, Promoted},
    thir,
    ty::{subst::InternalSubsts, GenericArg, ParamEnv, SubstsRef, Ty, TyCtxt, Visibility},
};
use rustc_span::{RealFileName, Span, Symbol, DUMMY_SP};
use rustc_trait_selection::traits::SelectionContext;
pub(crate) use util::{module_name, ItemType};
use why3::exp::Exp;

pub(crate) use crate::translated_item::*;

macro_rules! queryish {
    ($name:ident, $res:ty, $builder:ident) => {
        pub(crate) fn $name(&mut self, item: DefId) -> $res {
            if self.$name.get(&item).is_none() {
                let res = self.$builder(item);
                self.$name.insert(item, res);
            };

            &self.$name[&item]
        }
    };
    ($name:ident, $res:ty, $builder:expr) => {
        pub(crate) fn $name(&mut self, item: DefId) -> $res {
            if self.$name.get(&item).is_none() {
                let res = ($builder)(self, item);
                self.$name.insert(item, res);
            };

            &self.$name[&item]
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BodyId {
    pub def_id: LocalDefId,
    pub promoted: Option<Promoted>,
}

impl BodyId {
    pub fn new(def_id: LocalDefId, promoted: Option<Promoted>) -> Self {
        BodyId { def_id, promoted }
    }

    pub fn def_id(self) -> DefId {
        self.def_id.to_def_id()
    }
}

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    representative_type: HashMap<DefId, DefId>, // maps type ids to their 'representative type'
    ty_binding_groups: HashMap<DefId, IndexSet<DefId>>,
    laws: IndexMap<DefId, Vec<DefId>>,
    fmir_body: IndexMap<BodyId, fmir::Body<'tcx>>,
    terms: IndexMap<DefId, Term<'tcx>>,
    pub externs: Metadata<'tcx>,
    pub(crate) opts: Options,
    creusot_items: CreusotItems,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    extern_spec_items: HashMap<LocalDefId, DefId>,
    trait_impl: HashMap<DefId, TraitImpl<'tcx>>,
    sig: HashMap<DefId, PreSignature<'tcx>>,
    bodies: HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>,
    opacity: HashMap<DefId, Opacity>,
}

#[derive(Copy, Clone)]
pub(crate) struct Opacity(Visibility<DefId>);

impl Opacity {
    pub(crate) fn scope(self) -> Option<DefId> {
        match self.0 {
            Visibility::Public => None,
            Visibility::Restricted(modl) => Some(modl),
        }
    }
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
            externs: Default::default(),
            terms: Default::default(),
            creusot_items,
            opts,
            representative_type: Default::default(),
            ty_binding_groups: Default::default(),
            extern_specs: Default::default(),
            extern_spec_items: Default::default(),
            fmir_body: Default::default(),
            trait_impl: Default::default(),
            sig: Default::default(),
            bodies: Default::default(),
            opacity: Default::default(),
        }
    }

    pub(crate) fn load_metadata(&mut self) {
        self.externs.load(self.tcx, &self.opts.extern_paths);
    }

    queryish!(trait_impl, &TraitImpl<'tcx>, translate_impl);

    pub(crate) fn fmir_body(&mut self, body_id: BodyId) -> Option<&fmir::Body<'tcx>> {
        if !self.fmir_body.contains_key(&body_id) {
            let fmir = translation::function::fmir(self, body_id);
            self.fmir_body.insert(body_id, fmir);
        }
        self.fmir_body.get(&body_id)
    }

    pub(crate) fn term(&mut self, def_id: DefId) -> Option<&Term<'tcx>> {
        if !def_id.is_local() {
            return self.externs.term(def_id);
        }

        if util::has_body(self, def_id) {
            if !self.terms.contains_key(&def_id) {
                let mut term = pearlite::pearlite(self, def_id.expect_local())
                    .unwrap_or_else(|e| e.emit(self.tcx.sess));
                pearlite::normalize(self.tcx, self.param_env(def_id), &mut term);

                self.terms.insert(def_id, term);
            };
            self.terms.get(&def_id)
        } else {
            None
        }
    }

    queryish!(sig, &PreSignature<'tcx>, |ctx: &mut Self, key| {
        let mut term = pre_sig_of(&mut *ctx, key);
        term = term.normalize(ctx.tcx, ctx.param_env(key));
        term
    });

    pub(crate) fn body(&mut self, body_id: BodyId) -> &Body<'tcx> {
        let body = self.body_with_facts(body_id.def_id);
        match body_id.promoted {
            None => &body.body,
            Some(promoted) => &body.promoted.get(promoted).unwrap(),
        }
    }

    pub(crate) fn body_with_facts(&mut self, def_id: LocalDefId) -> &BodyWithBorrowckFacts<'tcx> {
        if !self.bodies.contains_key(&def_id) {
            let body = callbacks::get_body(self.tcx, def_id).unwrap();

            // Basic clean up, replace FalseEdges with Gotos. Could potentially also replace other statement with Nops.
            // Investigate if existing MIR passes do this as part of 'post borrowck cleanup'.
            // CleanupPostBorrowck.run_pass(self.tcx, &mut body.body);
            // SimplifyCfg::new("verify").run_pass(self.tcx, &mut body.body);

            self.bodies.insert(def_id, body);
        };

        self.bodies.get(&def_id).unwrap()
    }

    pub(crate) fn type_invariant(
        &self,
        def_id: DefId,
        ty: Ty<'tcx>,
    ) -> Option<(DefId, SubstsRef<'tcx>)> {
        let param_env = self.param_env(def_id);
        let ty = self.try_normalize_erasing_regions(param_env, ty).ok()?;

        if util::is_open_ty_inv(self.tcx, def_id)
            || ty_inv::is_tyinv_trivial(self.tcx, param_env, ty)
        {
            None
        } else {
            debug!("resolving type invariant of {ty:?} in {def_id:?}");
            let inv_did = self.get_diagnostic_item(Symbol::intern("creusot_invariant_internal"))?;
            let substs = self.mk_substs(&[GenericArg::from(ty)]);
            Some((inv_did, substs))
        }
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

    // Get the id of the type which represents a binding groups
    // Panics a type hasn't yet been translated
    pub(crate) fn representative_type(&self, def_id: DefId) -> DefId {
        *self.representative_type.get(&def_id).unwrap_or_else(|| panic!("no key for {:?}", def_id))
    }

    queryish!(laws, &[DefId], laws_inner);

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

    /// We encodes the opacity of functions using 'witnesses', funcitons that have the target opacity
    /// set as their *visibility*.
    pub(crate) fn opacity(&mut self, item: DefId) -> &Opacity {
        if self.opacity.get(&item).is_none() {
            self.opacity.insert(item, self.mk_opacity(item));
        };

        &self.opacity[&item]
    }

    fn mk_opacity(&self, item: DefId) -> Opacity {
        if !matches!(util::item_type(self.tcx, item), ItemType::Predicate | ItemType::Logic) {
            return Opacity(Visibility::Public);
        };

        let witness = util::opacity_witness_name(self.tcx, item)
            .and_then(|nm| self.creusot_item(nm))
            .map(|id| self.visibility(id))
            .unwrap_or_else(|| Visibility::Restricted(parent_module(self.tcx, item)));
        Opacity(witness)
    }

    /// Checks if `item` is transparent in the scope of `modl`.
    /// This will determine whether the solvers are allowed to unfold the body's definition.
    pub(crate) fn is_transparent_from(&mut self, item: DefId, modl: DefId) -> bool {
        self.opacity(item).0.is_accessible_from(modl, self.tcx)
    }

    pub(crate) fn metadata(&self) -> BinaryMetadata<'tcx> {
        BinaryMetadata::from_parts(&self.terms, &self.creusot_items, &self.extern_specs)
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
                self.mk_predicates(&additional_predicates),
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

        // If we ask for relative paths and the paths comes from the standard library, then we prefer returning
        // None, since the relative path of the stdlib is not stable.
        let path = match (&self.opts.span_mode, path) {
            (SpanMode::Relative, RealFileName::Remapped { .. }) => return None,
            _ => path.local_path_if_available(),
        };

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
        if let Some(attr) = self.span_attr(span) {
            Exp::Attr(attr, Box::new(exp))
        } else {
            exp
        }
    }

    pub(crate) fn check_purity(&mut self, def_id: LocalDefId) {
        let (thir, expr) =
            self.tcx.thir_body(def_id).unwrap_or_else(|_| Error::from(CrErr).emit(self.tcx.sess));
        let thir = thir.borrow();
        if thir.exprs.is_empty() {
            Error::new(self.tcx.def_span(def_id), "type checking failed").emit(self.tcx.sess);
        }

        let def_id = def_id.to_def_id();
        let in_pure_ctx = crate::util::is_spec(self.tcx, def_id)
            || crate::util::is_logic(self.tcx, def_id)
            || crate::util::is_predicate(self.tcx, def_id);

        if !in_pure_ctx && crate::util::is_no_translate(self.tcx, def_id) {
            return;
        }

        thir::visit::walk_expr(
            &mut PurityVisitor { tcx: self.tcx, thir: &thir, in_pure_ctx },
            &thir[expr],
        );
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

pub(crate) fn parent_module(tcx: TyCtxt, mut id: DefId) -> DefId {
    while tcx.def_kind(id) != DefKind::Mod {
        id = tcx.parent(id);
    }

    id
}
