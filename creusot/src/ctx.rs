use crate::{
    backend::ty_inv::is_tyinv_trivial,
    callbacks,
    contracts_items::{
        Intrinsic, function_has_logical_alias, gather_intrinsics, get_creusot_item, is_extern_spec,
        is_logic, is_opaque, is_open_inv_param, is_prophetic, opacity_witness_name,
    },
    metadata::{BinaryMetadata, Metadata, encode_def_ids, get_erasure_required},
    naming::variable_name,
    translation::{
        self,
        external::{
            ExternSpec, extract_erasure_from_child, extract_erasure_from_item,
            extract_extern_specs_from_item,
        },
        fmir,
        pearlite::{self, ScopedTerm},
        specification::{ContractClauses, PreSignature, inherited_extern_spec, pre_sig_of},
        traits::{Refinement, TraitResolved},
    },
    util::{erased_identity_for_item, parent_module},
    validate::AnfBlock,
};
use creusot_args::options::Options;
use indexmap::{IndexMap, IndexSet};
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
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Promoted,
    thir,
    ty::{
        Clause, GenericArg, GenericArgKind, GenericArgsRef, ParamEnv, Predicate,
        ResolverAstLowering, Ty, TyCtxt, TypingEnv, TypingMode, Visibility,
    },
};
use rustc_span::{DUMMY_SP, Span, Symbol};
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
pub(crate) enum Opacity {
    Opaque,
    Transparent(Visibility<DefId>),
}

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

pub type Thir<'tcx> = (thir::Thir<'tcx>, thir::ExprId);

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    raw_intrinsics: HashMap<Symbol, DefId>,
    pub intrinsic2did: HashMap<Intrinsic, DefId>,
    did2intrinsic: HashMap<DefId, Intrinsic>,
    pub externs: Metadata<'tcx>,
    pub(crate) opts: Options,
    creusot_items: HashMap<Symbol, DefId>,
    local_thir: IndexMap<LocalDefId, Thir<'tcx>>,
    /// This field tracks recursive calls, where we should check that a variant
    /// decreases.
    pub(crate) variant_calls: RefCell<IndexMap<DefId, IndexSet<DefId>>>,
    erasure_required: RefCell<IndexSet<DefId>>,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    extern_spec_items: HashMap<LocalDefId, DefId>,
    erased_local_defid: HashMap<LocalDefId, Erasure<'tcx>>,
    erasures_to_check: Vec<(LocalDefId, Erasure<'tcx>)>,
    params_open_inv: HashMap<DefId, Vec<usize>>,
    laws: OnceMap<DefId, Box<Vec<DefId>>>,
    /// Maps the [`DefId`] of a program function `f` with a `#[has_logical_alias(f')]`
    /// attribute to the logical function `f'`
    logical_aliases: HashMap<DefId, (Span, DefId)>,
    fmir_body: OnceMap<BodyId, Box<fmir::Body<'tcx>>>,
    terms: OnceMap<DefId, Box<Option<ScopedTerm<'tcx>>>>,
    trait_impl: OnceMap<DefId, Box<Vec<Refinement<'tcx>>>>,
    sig: OnceMap<DefId, Box<PreSignature<'tcx>>>,
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

pub(crate) fn gather_params_open_inv(tcx: TyCtxt) -> HashMap<DefId, Vec<usize>> {
    struct VisitFns<'tcx, 'a>(TyCtxt<'tcx>, HashMap<DefId, Vec<usize>>, &'a ResolverAstLowering);
    impl<'a> Visitor<'a> for VisitFns<'_, 'a> {
        fn visit_fn(&mut self, fk: FnKind<'a>, _: Span, node: NodeId) {
            let decl = match fk {
                FnKind::Fn(_, _, Fn { sig: FnSig { decl, .. }, .. }) => decl,
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
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        opts: Options,
        local_thir: IndexMap<LocalDefId, Thir<'tcx>>,
        params_open_inv: HashMap<DefId, Vec<usize>>,
    ) -> Self {
        let creusot_items = tcx
            .hir_body_owners()
            .filter_map(|did| {
                let did = did.to_def_id();
                Some((get_creusot_item(tcx, did)?, did))
            })
            .collect();

        let mut externs = Metadata::default();
        externs.load(tcx, &opts.extern_paths);

        let (raw_intrinsics, intrinsic2did, did2intrinsic) = gather_intrinsics(tcx, &externs);

        Self {
            tcx,
            raw_intrinsics,
            intrinsic2did,
            did2intrinsic,
            laws: Default::default(),
            externs,
            logical_aliases: Default::default(),
            terms: Default::default(),
            creusot_items,
            variant_calls: RefCell::new(IndexMap::new()),
            opts,
            local_thir,
            erasure_required: Default::default(),
            extern_specs: Default::default(),
            extern_spec_items: Default::default(),
            erased_local_defid: Default::default(),
            erasures_to_check: Default::default(),
            fmir_body: Default::default(),
            trait_impl: Default::default(),
            sig: Default::default(),
            opacity: Default::default(),
            params_open_inv,
            renamer: Default::default(),
            corenamer: Default::default(),
            crate_name: Default::default(),
        }
    }

    pub(crate) fn intrinsic(&self, did: DefId) -> Intrinsic {
        self.did2intrinsic.get(&did).copied().unwrap_or(Intrinsic::None)
    }

    pub(crate) fn int_ty(&self) -> Ty<'tcx> {
        self.type_of(Intrinsic::Int.get(self)).no_bound_vars().unwrap()
    }

    /// Returns `true` if a call from `caller` to `callee` should be checked to
    /// have decreased a variant.
    pub(crate) fn should_check_variant_decreases(&self, caller: DefId, callee: DefId) -> bool {
        self.variant_calls.borrow().get(&caller).is_some_and(|calls| calls.contains(&callee))
    }

    /// If this returns `None`, there must have been a type error in the body.
    /// Callers can then skip whatever they were doing silently because Creusot will abort in the end (in `after_analysis`).
    pub(crate) fn get_local_thir(
        &self,
        def_id: LocalDefId,
    ) -> Option<&(thir::Thir<'tcx>, thir::ExprId)> {
        self.local_thir.get(&def_id)
    }

    pub(crate) fn erased_thir(&self, def_id: DefId) -> Option<&AnfBlock<'tcx>> {
        self.erasure_required.borrow_mut().insert(def_id);
        self.externs.erased_thir(def_id)
    }

    pub(crate) fn iter_local_thir(
        &self,
    ) -> impl Iterator<Item = (&LocalDefId, &(thir::Thir<'tcx>, thir::ExprId))> {
        self.local_thir.iter()
    }

    /// Get the _logical alias_ of the given program function, if any.
    ///
    /// Logical aliases are defined with the `#[has_logical_alias(...)]` attribute.
    ///
    /// The returned span is the span of the attribute.
    pub(crate) fn logical_alias(&self, def_id: DefId) -> Option<(Span, DefId)> {
        self.logical_aliases.get(&def_id).copied()
    }

    /// Load all the logical aliases defined in the current crate
    ///
    /// They can later be retrieved using [`Self::logical_alias`].
    pub(crate) fn load_logical_aliases(&mut self) {
        // FIXME: what about functions from another crate?
        let tcx = self.tcx;
        for local_id in self.hir_body_owners() {
            let def_id = local_id.to_def_id();
            // TODO: Put this in another file for better organisation
            if let Some((span, logic_id)) = function_has_logical_alias(self, def_id) {
                let program_span = tcx.def_span(def_id);
                let logic_span = tcx.def_span(logic_id);
                let program_subst = erased_identity_for_item(tcx, def_id);
                let logic_subst = erased_identity_for_item(tcx, logic_id);
                let mut program_subst = program_subst.iter().map(|arg| arg.kind());
                let mut logic_subst = logic_subst.iter().map(|arg| arg.kind());
                loop {
                    let prog_arg = program_subst.next();
                    let logic_arg = logic_subst.next();
                    match (prog_arg, logic_arg) {
                        (None, None) => break,
                        (Some(arg), None) | (None, Some(arg)) => {
                            tcx.dcx()
                                    .struct_span_err(
                                        span,
                                        format!(
                                            "mismatched generic parameters for logical alias: {} parameter {arg:?} in the alias",
                                            if prog_arg.is_some() {
                                                "missing"
                                            } else {
                                                "additional"
                                            }),
                                    )
                                    .with_span_note(program_span, "function defined here")
                                    .with_span_note(logic_span, "logical alias defined here")
                                    .emit();
                        }
                        (Some(GenericArgKind::Type(t1)), Some(GenericArgKind::Type(t2))) => {
                            if t1 != t2 {
                                tcx.dcx().struct_span_err(span, format!("mismatched types in logical alias: expected {t1}, got {t2}"))
                                        .with_span_note(program_span, "function defined here")
                                        .with_span_note(logic_span, "logical alias defined here")
                                        .emit();
                            }
                        }
                        (Some(GenericArgKind::Const(c1)), Some(GenericArgKind::Const(c2))) => {
                            let (t1, name1) = match c1.kind() {
                                rustc_type_ir::ConstKind::Param(p) => {
                                    (p.find_const_ty_from_env(tcx.param_env(def_id)), p.name)
                                }
                                _ => unreachable!(),
                            };
                            let (t2, name2) = match c2.kind() {
                                rustc_type_ir::ConstKind::Param(p) => {
                                    (p.find_const_ty_from_env(tcx.param_env(logic_id)), p.name)
                                }
                                _ => unreachable!(),
                            };
                            if t1 != t2 {
                                tcx.dcx()
                                        .struct_span_err(
                                            span,
                                           format!("mismatched types of constants: expected {t1} (constant {name1}), got {t2} (constant {name2})"),
                                        )
                                        .with_span_note(program_span, "function defined here")
                                        .with_span_note(logic_span, "logical function defined here")
                                        .emit();
                            }
                        }
                        (
                            Some(GenericArgKind::Lifetime(l1)),
                            Some(GenericArgKind::Lifetime(l2)),
                        ) => {
                            if l1 != l2 {
                                tcx.dcx()
                                        .struct_span_err(
                                            span,
                                            "mismatched lifetime parameters for logical alias: expected {l1}, got {l2}",
                                        )
                                        .with_span_note(program_span, "function defined here")
                                        .with_span_note(logic_span, "logical function defined here")
                                        .emit();
                            }
                        }
                        (Some(a1), Some(a2)) => {
                            tcx.dcx()
                                    .struct_span_err(span, format!("mismatched parameter kinds for logical alias: expected {a1:?}, got {a2:?}"))
                                    .with_span_note(program_span, "function defined here")
                                    .with_span_note(logic_span, "logical function defined here")
                                    .emit();
                        }
                    }
                }
                let bounds1 = tcx.param_env(def_id).caller_bounds();
                let bounds2 = tcx.param_env(logic_id).caller_bounds();
                if bounds1 != bounds2 {
                    let mut err = tcx
                        .dcx()
                        .struct_span_err(span, "mismatched trait bounds for logical alias");
                    for (b1, b2) in std::iter::zip(bounds1.iter().rev(), bounds2.iter().rev()) {
                        if b1 != b2 {
                            err.note(format!("{b1} != {b2}"));
                        }
                    }
                    if bounds1.len() < bounds2.len() {
                        for b in bounds2.iter().rev().skip(bounds1.len()) {
                            err.note(format!("additional bound {b} found"));
                        }
                    } else if bounds1.len() > bounds2.len() {
                        for b in bounds1.iter().rev().skip(bounds2.len()) {
                            err.note(format!("missing bound {b}"));
                        }
                    }
                    err.with_span_note(program_span, "function defined here")
                        .with_span_note(logic_span, "logical function defined here")
                        .emit();
                }

                // the aliased function must also comes from the current crate
                if !logic_id.is_local() {
                    tcx.dcx()
                        .struct_span_err(
                            program_span,
                            "The aliased logical function should be defined in the same crate",
                        )
                        .with_span_note(logic_span, "aliased function defined here")
                        .emit();
                }
                // When defining an alias, neither functions must be a trait function
                if tcx.trait_of_assoc(def_id).is_some() {
                    tcx.dcx().span_err(
                        program_span,
                        "Cannot make a logical alias from a trait function",
                    );
                }
                if tcx.trait_of_assoc(logic_id).is_some() {
                    tcx.dcx()
                        .span_err(logic_span, "Cannot make a logical alias to a trait function");
                }
                if tcx.dcx().has_errors().is_some() {
                    continue;
                }

                trace!(
                    "`{}` is an alias for `{}`",
                    self.def_path_str(local_id),
                    self.def_path_str(logic_id),
                );
                self.logical_aliases.insert(def_id, (span, logic_id));
            }
        }
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
                if self.tcx.hir_maybe_body_owned_by(local_id).is_some() {
                    let (bound, term) = match pearlite::pearlite(self, local_id) {
                        Ok(t) => t,
                        Err(err) => err.abort(self.tcx),
                    };
                    let bound = bound.iter().map(|b| b.0).collect();
                    Box::new(Some(ScopedTerm(
                        bound,
                        pearlite::normalize(self, self.typing_env(def_id), term),
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
        callbacks::get_body(self.tcx, def_id)
    }

    /// `span` is used for diagnostics.
    pub(crate) fn type_invariant(
        &self,
        typing_env: TypingEnv<'tcx>,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        let ty = self.normalize_erasing_regions(typing_env, ty);
        if is_tyinv_trivial(self, typing_env, ty, span) {
            None
        } else {
            let substs = self.mk_args(&[GenericArg::from(ty)]);
            Some((Intrinsic::Inv.get(self), substs))
        }
    }

    pub(crate) fn resolve(
        &self,
        typing_env: TypingEnv<'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        let trait_meth_id = Intrinsic::ResolveMethod.get(self);
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

        Some((Intrinsic::Resolve.get(self), substs))
    }

    queryish!(laws, DefId, [DefId], laws_inner);

    // TODO Make private
    pub(crate) fn extern_spec(&self, def_id: DefId) -> Option<&ExternSpec<'tcx>> {
        self.extern_specs.get(&def_id).or_else(|| self.externs.extern_spec(def_id))
    }

    queryish!(opacity, DefId, Opacity, mk_opacity);

    /// We encodes the opacity of functions using 'witnesses', functions that have the target opacity
    /// set as their *visibility*.
    fn mk_opacity(&self, item: DefId) -> Opacity {
        match self.item_type(item) {
            ItemType::Constant => Opacity::Transparent(Visibility::Public),
            ItemType::Logic { .. } if is_opaque(self.tcx, item) => Opacity::Opaque,
            ItemType::Logic { .. } => {
                let vis = opacity_witness_name(self.tcx, item).map_or_else(
                    || Visibility::Restricted(parent_module(self.tcx, item)),
                    |nm| self.visibility(self.creusot_item(nm).unwrap()),
                );
                Opacity::Transparent(vis)
            }
            _ => unreachable!(),
        }
    }

    /// Checks if `item` is transparent in the scope of `scope`.
    /// This will determine whether the solvers are allowed to unfold the body's definition.
    pub(crate) fn is_transparent_from(&self, item: DefId, mut scope: DefId) -> bool {
        match self.opacity(item) {
            Opacity::Transparent(vis) => vis.is_accessible_from(scope, self.tcx),
            Opacity::Opaque => loop {
                if item == scope {
                    return true;
                }
                if let Some(s) = self.tcx.opt_parent(scope) {
                    scope = s;
                } else {
                    return false;
                }
            },
        }
    }

    fn exported_erased_thir(&mut self) -> Vec<(DefId, AnfBlock<'tcx>)> {
        if self.opts.erasure_check.is_no() {
            return vec![];
        }
        let Some(erasure_check_dir) = &self.opts.erasure_check_dir else { return vec![] };
        let erasure_required = get_erasure_required(self.tcx, erasure_check_dir);
        if erasure_required.is_empty() {
            return vec![];
        }
        self.local_thir
            .iter()
            .filter_map(|(local_id, thir)| {
                if erasure_required.contains(local_id) {
                    let erasure = crate::validate::a_normal_form_for_export(self, *local_id, thir)?;
                    Some((local_id.to_def_id(), erasure))
                } else {
                    None
                }
            })
            .collect()
    }

    /// This must only be called at the end because it will `take` stuff out of `self`.
    pub(crate) fn metadata(mut self) -> BinaryMetadata<'tcx> {
        let erased_thir = self.exported_erased_thir();
        BinaryMetadata::from_parts(
            self.terms,
            self.creusot_items,
            self.raw_intrinsics,
            self.extern_specs,
            self.params_open_inv,
            erased_thir,
            self.erased_local_defid,
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
            self.tcx.hir_maybe_body_owned_by(local_id).is_some()
        } else {
            match self.item_type(def_id) {
                ItemType::Logic { .. } => self.term(def_id).is_some(),
                _ => false,
            }
        }
    }

    pub(crate) fn load_extern_specs(&mut self) {
        let mut traits_or_impls = Vec::new();

        for (&def_id, thir) in self.local_thir.iter() {
            if is_extern_spec(self.tcx, def_id.to_def_id()) {
                if let Some(container) = self.opt_associated_item(def_id.to_def_id()) {
                    traits_or_impls.push(container.def_id)
                }

                let (i, es) = extract_extern_specs_from_item(self, def_id, thir);

                if self.extern_spec(i).is_some() {
                    self.crash_and_error(
                        self.def_span(def_id),
                        format!("duplicate extern specification for {}", self.def_path_str(i)),
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

            self.extern_specs.insert(
                def_id,
                ExternSpec {
                    contract: ContractClauses::new(),
                    subst: erased_identity_for_item(self.tcx, def_id),
                    inputs: Box::new([]),
                    output: Ty::new_bool(self.tcx), // dummy
                    additional_predicates,
                },
            );
        }
    }

    pub(crate) fn load_erasures(&mut self) {
        for (&def_id, thir) in self.local_thir.iter() {
            let Some((eraser, erasure, to_check)) = extract_erasure_from_item(self, def_id, thir)
            else {
                continue;
            };
            self.erased_local_defid.insert(eraser, erasure);
            if let Some(to_check) = to_check {
                self.erasures_to_check.push((eraser, to_check));
            }
        }
        if self.erasures_to_check.is_empty() {
            return;
        }
        for (&def_id, _) in self.local_thir.iter() {
            if let Some(erasure) = extract_erasure_from_child(self, def_id) {
                self.erased_local_defid.insert(def_id, erasure.clone());
                self.erasures_to_check.push((def_id, erasure));
            }
        }
    }

    pub(crate) fn iter_erasures_to_check(
        &self,
    ) -> impl Iterator<Item = &(LocalDefId, Erasure<'tcx>)> {
        self.erasures_to_check.iter()
    }

    pub(crate) fn write_erasure_required(&self) {
        if !self.opts.should_output {
            // Skip if this is not a primary package
            return;
        }
        let Some(erasure_check_dir) = &self.opts.erasure_check_dir else {
            return;
        };
        let path = erasure_check_dir.join(self.tcx.crate_name(LOCAL_CRATE).as_str());
        let erasure_required = self.erasure_required.borrow();
        if erasure_required.is_empty() {
            let _ = std::fs::remove_file(path);
            return;
        }
        std::fs::create_dir_all(erasure_check_dir)
            .and_then(|_| encode_def_ids(self.tcx, &path, erasure_required.iter()))
            .unwrap_or_else(|e| {
                self.crash_and_error(DUMMY_SP, format!("could not write {}: {}", path.display(), e))
            });
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
            let r = Ident::fresh(self.crate_name(), variable_name(self.hir_name(ident).as_str()));
            self.corenamer.borrow_mut().insert(r, ident);
            r
        })
    }

    pub(crate) fn crate_name(&self) -> why3::Symbol {
        *self.crate_name.get_or_init(|| crate_name(self.tcx))
    }

    pub(crate) fn erasure(&self, def_id: DefId) -> Option<&Erasure<'tcx>> {
        match def_id.as_local() {
            Some(local) => self.erased_local_defid.get(&local),
            None => self.externs.erasure(def_id),
        }
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

#[derive(Clone, Debug, TyDecodable, TyEncodable)]
pub struct Erasure<'tcx> {
    /// `DefId` of the trait method or standalone `fn` item
    /// For `#[erasure]` checking of calling functions.
    pub def: (DefId, GenericArgsRef<'tcx>),
    /// `true` for ghost arguments to erase
    pub erase_args: Vec<bool>,
}
