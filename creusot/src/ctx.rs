use crate::{
    backend::ty_inv::is_tyinv_trivial,
    callbacks,
    contracts_items::{
        get_creusot_item, get_inv_function, get_resolve_function, get_resolve_method,
        is_extern_spec, is_logic, is_open_inv_param, is_prophetic, opacity_witness_name,
    },
    metadata::{BinaryMetadata, Metadata},
    naming::variable_name,
    options::Options,
    translation::{
        self,
        external::{ExternSpec, extract_extern_specs_from_item},
        fmir,
        pearlite::{self, ScopedTerm},
        specification::{ContractClauses, PreSignature, inherited_extern_spec, pre_sig_of},
        traits::{Refinement, TraitResolved},
    },
    util::{erased_identity_for_item, parent_module},
};
use indexmap::IndexMap;
use once_map::unsync::OnceMap;
use rustc_ast::{
    Fn, FnSig, NodeId,
    visit::{FnKind, Visitor, walk_fn},
};
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_errors::{Diag, DiagMessage, FatalAbort};
use rustc_hir::{
    HirId,
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE, LocalDefId},
};
use rustc_infer::traits::ObligationCause;
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{Promoted, TerminatorKind},
    thir,
    ty::{
        Clause, GenericArg, GenericArgsRef, ParamEnv, Predicate, ResolverAstLowering, Ty, TyCtxt,
        TypingEnv, TypingMode, Visibility,
    },
};
use rustc_span::{Span, Symbol};
use rustc_trait_selection::traits::normalize_param_env_or_error;
use rustc_type_ir::inherent::Ty as _;
use std::{
    cell::{OnceCell, RefCell},
    collections::HashMap,
    ops::Deref,
};
use why3::Ident;

pub(crate) use crate::{backend::clone_map::*, translated_item::*};

macro_rules! queryish {
    ($name:ident, $key:ty, $res:ty, $builder:ident) => {
        pub(crate) fn $name(&self, item: $key) -> &$res {
            self.$name.insert(item, |&item| Box::new(self.$builder(item)))
        }
    };
    ($name:ident, $key:ty, $res:ty, $builder:expr) => {
        pub(crate) fn $name(&self, item: $key) -> &$res {
            self.$name.insert(item, |&item| Box::new(($builder)(self, item)))
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, TypeVisitable, TypeFoldable)]
pub struct BodyId {
    pub def_id: DefId,
    pub promoted: Option<Promoted>,
}

impl BodyId {
    pub fn local(def_id: LocalDefId) -> Self {
        BodyId { def_id: def_id.to_def_id(), promoted: None }
    }

    pub fn from_def_id(def_id: DefId) -> Self {
        BodyId { def_id, promoted: None }
    }
}

#[derive(Copy, Clone)]
pub(crate) struct Opacity(pub Visibility<DefId>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemType {
    Logic { prophetic: bool },
    Program,
    Closure,
    Trait,
    Impl,
    Type,
    AssocTy,
    Constant,
    Variant,
    Unsupported(DefKind),
    Field,
}

impl ItemType {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            ItemType::Logic { prophetic: false } => "logic function",
            ItemType::Logic { prophetic: true } => "prophetic logic function",
            ItemType::Program => "program function",
            ItemType::Closure => "closure",
            ItemType::Trait => "trait declaration",
            ItemType::Impl => "trait implementation",
            ItemType::Type => "type declaration",
            ItemType::AssocTy => "associated type",
            ItemType::Constant => "constant",
            ItemType::Field => "field",
            ItemType::Unsupported(_) => "[OTHER]",
            ItemType::Variant => "constructor",
        }
    }

    pub(crate) fn can_implement(self, trait_type: Self) -> bool {
        match (self, trait_type) {
            (ItemType::Logic { prophetic: false }, ItemType::Logic { prophetic: true }) => true,
            _ => self == trait_type,
        }
    }
}

pub trait HasTyCtxt<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;

    fn crash_and_error(&self, span: Span, msg: impl Into<DiagMessage>) -> ! {
        // TODO: try to add a code back in
        self.tcx().dcx().span_fatal(span, msg)
    }

    fn fatal_error(&self, span: Span, msg: impl Into<DiagMessage>) -> Diag<'tcx, FatalAbort> {
        // TODO: try to add a code back in
        self.tcx().dcx().struct_span_fatal(span, msg)
    }

    fn error(
        &self,
        span: Span,
        msg: impl Into<DiagMessage>,
    ) -> Diag<'tcx, rustc_errors::ErrorGuaranteed> {
        self.tcx().dcx().struct_span_err(span, msg)
    }

    fn warn(&self, span: Span, msg: impl Into<DiagMessage>) {
        self.tcx().dcx().span_warn(span, msg)
    }

    fn span_bug(&self, span: Span, msg: impl Into<String>) -> ! {
        self.tcx().dcx().span_bug(span, msg.into())
    }
}

impl<'tcx> HasTyCtxt<'tcx> for TyCtxt<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        *self
    }
}

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,

    pub externs: Metadata<'tcx>,
    pub(crate) opts: Options,
    creusot_items: HashMap<Symbol, DefId>,
    pub(crate) thir: IndexMap<LocalDefId, (thir::Thir<'tcx>, thir::ExprId)>,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    extern_spec_items: HashMap<LocalDefId, DefId>,
    params_open_inv: HashMap<DefId, Vec<usize>>,
    laws: OnceMap<DefId, Box<Vec<DefId>>>,
    fmir_body: OnceMap<BodyId, Box<fmir::Body<'tcx>>>,
    terms: OnceMap<DefId, Box<Option<ScopedTerm<'tcx>>>>,
    trait_impl: OnceMap<DefId, Box<Vec<Refinement<'tcx>>>>,
    sig: OnceMap<DefId, Box<PreSignature<'tcx>>>,
    bodies: OnceMap<LocalDefId, Box<BodyWithBorrowckFacts<'tcx>>>,
    opacity: OnceMap<DefId, Box<Opacity>>,
    renamer: RefCell<HashMap<HirId, Ident>>,
    pub corenamer: RefCell<HashMap<Ident, HirId>>,
    crate_name: OnceCell<why3::Symbol>,
}

impl<'tcx> Deref for TranslationCtx<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

fn gather_params_open_inv(tcx: TyCtxt) -> HashMap<DefId, Vec<usize>> {
    struct VisitFns<'tcx, 'a>(TyCtxt<'tcx>, HashMap<DefId, Vec<usize>>, &'a ResolverAstLowering);
    impl<'a> Visitor<'a> for VisitFns<'_, 'a> {
        fn visit_fn(&mut self, fk: FnKind<'a>, _: Span, node: NodeId) {
            let decl = match fk {
                FnKind::Fn(_, _, _, Fn { sig: FnSig { decl, .. }, .. }) => decl,
                FnKind::Closure(_, _, decl, _) => decl,
            };
            let mut open_inv_params = vec![];
            for (i, p) in decl.inputs.iter().enumerate() {
                if is_open_inv_param(self.0, p) {
                    open_inv_params.push(i);
                }
            }
            let defid = self.2.node_id_to_def_id[&node].to_def_id();
            assert!(self.1.insert(defid, open_inv_params).is_none());
            walk_fn(self, fk)
        }
    }

    let (resolver, cr) = &*tcx.resolver_for_lowering().borrow();

    let mut visit = VisitFns(tcx, HashMap::new(), resolver);
    visit.visit_crate(cr);
    visit.1
}

impl<'tcx> TranslationCtx<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: Options) -> Self {
        let params_open_inv = gather_params_open_inv(tcx);
        let creusot_items = tcx
            .hir()
            .body_owners()
            .filter_map(|did| {
                let did = did.to_def_id();
                Some((get_creusot_item(tcx, did)?, did))
            })
            .collect();

        Self {
            tcx,
            laws: Default::default(),
            externs: Default::default(),
            terms: Default::default(),
            creusot_items,
            opts,
            extern_specs: Default::default(),
            extern_spec_items: Default::default(),
            fmir_body: Default::default(),
            trait_impl: Default::default(),
            sig: Default::default(),
            bodies: Default::default(),
            opacity: Default::default(),
            params_open_inv,
            renamer: Default::default(),
            corenamer: Default::default(),
            crate_name: Default::default(),
            thir: Default::default(),
        }
    }

    pub(crate) fn load_metadata(&mut self) {
        self.externs.load(self.tcx, &self.opts.extern_paths);
    }

    /// Clone all THIR bodies before they are stolen by `analysis`
    pub(crate) fn clone_all_thir(&mut self) {
        for def_id in self.tcx.hir().body_owners() {
            // If a body is missing, it means that there was an error, and we know that because `Err` is `ErrorGuaranteed`.
            // Keep going. We will abort later in `translation::after_analysis` after doing more checks that could raise more errors.
            if let Ok((thir, expr0)) = self.tcx.thir_body(def_id) {
                self.thir.insert(def_id, (thir.borrow().clone(), expr0));
            }
        }
    }

    /// If this returns `None`, there must have been a type error in the body.
    /// Callers can then skip whatever they were doing silently because Creusot will abort in the end (in `after_analysis`).
    pub(crate) fn get_thir(&self, def_id: LocalDefId) -> Option<(&thir::Thir<'tcx>, thir::ExprId)> {
        self.thir.get(&def_id).map(|&(ref thir, expr)| (thir, expr))
    }

    queryish!(trait_impl, DefId, Vec<Refinement<'tcx>>, translate_impl);

    queryish!(fmir_body, BodyId, fmir::Body<'tcx>, translation::function::fmir);

    /// Compute the pearlite term associated with `def_id`.
    ///
    /// # Returns
    /// - `None` if `def_id` does not have a body
    /// - `Some(term)` if `def_id` has a body, in this crate or in a dependency.
    pub(crate) fn term<'a>(&'a self, def_id: DefId) -> Option<&'a ScopedTerm<'tcx>> {
        let Some(local_id) = def_id.as_local() else {
            return self.externs.term(def_id);
        };

        self.terms
            .insert(def_id, |_| {
                if self.tcx.hir().maybe_body_owned_by(local_id).is_some() {
                    let (bound, term) = match pearlite::pearlite(self, local_id) {
                        Ok(t) => t,
                        Err(err) => err.abort(self.tcx),
                    };
                    let bound = bound.iter().map(|b| b.0).collect();
                    Box::new(Some(ScopedTerm(
                        bound,
                        pearlite::normalize(self.tcx, self.typing_env(def_id), term),
                    )))
                } else {
                    Box::new(None)
                }
            })
            .as_ref()
    }

    pub(crate) fn params_open_inv(&self, def_id: DefId) -> Option<&Vec<usize>> {
        if !def_id.is_local() {
            return self.externs.params_open_inv(def_id);
        }
        self.params_open_inv.get(&def_id)
    }

    queryish!(sig, DefId, PreSignature<'tcx>, (pre_sig_of));

    pub(crate) fn body_with_facts(&self, def_id: LocalDefId) -> &BodyWithBorrowckFacts<'tcx> {
        self.bodies.insert(def_id, |_| Box::new(body_with_facts(self.tcx, def_id)))
    }

    /// `span` is used for diagnostics.
    pub(crate) fn type_invariant(
        &self,
        typing_env: TypingEnv<'tcx>,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        let ty = self.normalize_erasing_regions(typing_env, ty);
        if is_tyinv_trivial(self.tcx, typing_env, ty, span) {
            None
        } else {
            let inv_did = get_inv_function(self.tcx);
            let substs = self.mk_args(&[GenericArg::from(ty)]);
            Some((inv_did, substs))
        }
    }

    pub(crate) fn resolve(
        &self,
        typing_env: TypingEnv<'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        let trait_meth_id = get_resolve_method(self.tcx);
        let substs = self.mk_args(&[GenericArg::from(ty)]);

        // Optimization: if we know there is no Resolve instance for this type, then we do not emit
        // a resolve
        if !ty.is_closure()
            && matches!(
                TraitResolved::resolve_item(self.tcx, typing_env, trait_meth_id, substs),
                TraitResolved::NoInstance
            )
        {
            return None;
        }

        Some((get_resolve_function(self.tcx), substs))
    }

    queryish!(laws, DefId, [DefId], laws_inner);

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

    queryish!(opacity, DefId, Opacity, mk_opacity);

    /// We encodes the opacity of functions using 'witnesses', functions that have the target opacity
    /// set as their *visibility*.
    fn mk_opacity(&self, item: DefId) -> Opacity {
        match self.item_type(item) {
            ItemType::Constant => Opacity(Visibility::Public),
            ItemType::Logic { .. } => Opacity(opacity_witness_name(self.tcx, item).map_or_else(
                || Visibility::Restricted(parent_module(self.tcx, item)),
                |nm| self.visibility(self.creusot_item(nm).unwrap()),
            )),
            _ => unreachable!(),
        }
    }

    /// Checks if `item` is transparent in the scope of `modl`.
    /// This will determine whether the solvers are allowed to unfold the body's definition.
    pub(crate) fn is_transparent_from(&self, item: DefId, modl: DefId) -> bool {
        self.opacity(item).0.is_accessible_from(modl, self.tcx)
    }

    pub(crate) fn metadata(&mut self) -> BinaryMetadata<'tcx> {
        BinaryMetadata::from_parts(
            &mut self.terms,
            &self.creusot_items,
            &self.extern_specs,
            &self.params_open_inv,
        )
    }

    pub(crate) fn creusot_item(&self, name: Symbol) -> Option<DefId> {
        self.creusot_items.get(&name).cloned().or_else(|| self.externs.creusot_item(name))
    }

    pub(crate) fn param_env(&self, def_id: DefId) -> ParamEnv<'tcx> {
        let (id, subst) = inherited_extern_spec(self, def_id)
            .unwrap_or_else(|| (def_id, erased_identity_for_item(self.tcx, def_id)));
        if let Some(es) = self.extern_spec(id) {
            let base_predicates =
                self.tcx.param_env(def_id).caller_bounds().into_iter().map(Clause::as_predicate);
            let additional_predicates = es.predicates_for(self.tcx, subst).into_iter();
            let clauses =
                base_predicates.chain(additional_predicates).map(Predicate::expect_clause);
            let res = ParamEnv::new(self.mk_clauses_from_iter(clauses));
            let res = normalize_param_env_or_error(self.tcx, res, ObligationCause::dummy());
            res
        } else {
            self.tcx.param_env(def_id)
        }
    }

    pub(crate) fn typing_env(&self, def_id: DefId) -> TypingEnv<'tcx> {
        // FIXME: is it correct to pretend we are doing a non-body analysis?
        let param_env = self.param_env(def_id);
        let mode = if self.is_mir_available(def_id) && def_id.is_local() {
            TypingMode::post_borrowck_analysis(self.tcx, def_id.as_local().unwrap())
        } else {
            TypingMode::non_body_analysis()
        };
        TypingEnv { typing_mode: mode, param_env }
    }

    pub(crate) fn has_body(&self, def_id: DefId) -> bool {
        if let Some(local_id) = def_id.as_local() {
            self.tcx.hir().maybe_body_owned_by(local_id).is_some()
        } else {
            match self.item_type(def_id) {
                ItemType::Logic { .. } => self.term(def_id).is_some(),
                _ => false,
            }
        }
    }

    pub(crate) fn load_extern_specs(&mut self) {
        let mut traits_or_impls = Vec::new();

        for (&def_id, thir) in self.thir.iter() {
            if is_extern_spec(self.tcx, def_id.to_def_id()) {
                if let Some(container) = self.opt_associated_item(def_id.to_def_id()) {
                    traits_or_impls.push(container.def_id)
                }

                let (i, es) = extract_extern_specs_from_item(self, def_id, thir);

                if self.extern_spec(i).is_some() {
                    self.crash_and_error(
                        self.def_span(def_id),
                        format!("duplicate extern specification for {i:?}"),
                    );
                };

                let _ = self.extern_specs.insert(i, es);

                self.extern_spec_items.insert(def_id, i);
            }
        }

        for def_id in traits_or_impls {
            let mut additional_predicates: Vec<_> = Vec::new();
            for item in self.associated_items(def_id).in_definition_order() {
                additional_predicates
                    .extend(self.extern_spec(item.def_id).unwrap().additional_predicates.clone());
            }
            // let additional_predicates = self.arena.alloc_slice(&additional_predicates);
            // let additional_predicates = rustc_middle::ty::GenericPredicates { parent: None, predicates: additional_predicates };

            self.extern_specs.insert(def_id, ExternSpec {
                contract: ContractClauses::new(),
                subst: erased_identity_for_item(self.tcx, def_id),
                inputs: Box::new([]),
                output: Ty::new_bool(self.tcx), // dummy
                additional_predicates,
            });
        }
    }

    pub(crate) fn item_type(&self, def_id: DefId) -> ItemType {
        match self.tcx.def_kind(def_id) {
            DefKind::Trait => ItemType::Trait,
            DefKind::Impl { .. } => ItemType::Impl,
            DefKind::Fn | DefKind::AssocFn => {
                if is_logic(self.tcx, def_id) {
                    ItemType::Logic { prophetic: is_prophetic(self.tcx, def_id) }
                } else {
                    ItemType::Program
                }
            }
            DefKind::AssocConst | DefKind::Const | DefKind::InlineConst | DefKind::ConstParam => {
                ItemType::Constant
            }
            DefKind::Closure => ItemType::Closure,
            DefKind::Struct | DefKind::Enum | DefKind::Union => ItemType::Type,
            DefKind::AssocTy => ItemType::AssocTy,
            DefKind::Field => ItemType::Field,
            DefKind::Variant => ItemType::Variant,
            dk => ItemType::Unsupported(dk),
        }
    }

    pub(crate) fn rename(&self, ident: HirId) -> Ident {
        *self.renamer.borrow_mut().entry(ident).or_insert_with(|| {
            let r = Ident::fresh(self.crate_name(), variable_name(self.hir().name(ident).as_str()));
            self.corenamer.borrow_mut().insert(r, ident);
            r
        })
    }

    pub(crate) fn crate_name(&self) -> why3::Symbol {
        *self.crate_name.get_or_init(|| crate_name(self.tcx))
    }
}

impl<'tcx> HasTyCtxt<'tcx> for TranslationCtx<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

pub fn crate_name(tcx: TyCtxt) -> why3::Symbol {
    tcx.crate_name(LOCAL_CRATE).as_str().into()
}

/// This should only be called at most once per `def_id` (for more info, see `callbacks::get_body`).
pub(crate) fn body_with_facts(tcx: TyCtxt, def_id: LocalDefId) -> BodyWithBorrowckFacts {
    let mut body = callbacks::get_body(tcx, def_id)
        .unwrap_or_else(|| panic!("did not find body for {def_id:?}"));

    // We need to remove false edges. They are used in compilation of pattern matchings
    // in ways that may result in move paths that are marked live and uninitilized at the
    // same time. We cannot handle this in the generation of resolution.
    // On the other hand, it is necessary to keep false unwind edges, because they are needed
    // by liveness analysis.
    for bbd in body.body.basic_blocks_mut().iter_mut() {
        let term = bbd.terminator_mut();
        if let TerminatorKind::FalseEdge { real_target, .. } = term.kind {
            term.kind = TerminatorKind::Goto { target: real_target };
        }
    }
    body
}
