use crate::{
    backend::resolve::is_resolve_trivial,
    callbacks,
    contracts_items::{
        Intrinsic, gather_intrinsics, get_creusot_item, is_extern_spec, is_logic, is_opaque,
        is_open_inv_param, is_prophetic, opacity_witness_name,
    },
    metadata::{BinaryMetadata, Metadata, encode_def_ids, get_erasure_required},
    naming::{ComaNames, ModulePath, lowercase_prefix},
    translation::{
        self,
        external::{
            ExternSpec, extract_erasure_from_child, extract_erasure_from_item,
            extract_extern_specs_from_item,
        },
        fmir,
        pearlite::{self, ScopedTerm, Term},
        specification::{ContractClauses, PreSignature, inherited_extern_spec, pre_sig_of},
        traits::Refinement,
    },
    util::{erased_identity_for_item, parent_module},
    validate::AnfBlock,
};
use creusot_args::options::Options;
use indexmap::{IndexMap, IndexSet};
use once_map::unsync::OnceMap;
use rustc_ast::{
    AttrVec, Fn, FnSig, NodeId,
    visit::{FnKind, Visitor, walk_fn},
};
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_data_structures::steal::Steal;
use rustc_errors::{Diag, DiagMessage, FatalAbort};
use rustc_hir::{
    HirId,
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE, LocalDefId},
};
use rustc_index::bit_set::DenseBitSet;
use rustc_infer::traits::ObligationCause;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Promoted,
    thir,
    ty::{
        self, Clause, GenericArg, GenericArgsRef, ParamEnv, Predicate, ResolverAstLowering, Ty,
        TyCtxt, TypingEnv, TypingMode, Visibility,
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

pub type ThirExpr<'tcx> = (&'tcx Steal<thir::Thir<'tcx>>, thir::ExprId);

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    raw_intrinsics: HashMap<Symbol, DefId>,
    pub intrinsic2did: HashMap<Intrinsic, DefId>,
    did2intrinsic: HashMap<DefId, Intrinsic>,
    pub externs: Metadata<'tcx>,
    pub(crate) opts: Options,
    creusot_items: HashMap<Symbol, DefId>,
    /// This field tracks recursive calls, where we should check that a variant
    /// decreases.
    pub(crate) variant_calls: RefCell<IndexMap<DefId, IndexSet<DefId>>>,
    erasure_required: RefCell<IndexSet<DefId>>,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    extern_spec_items: HashMap<LocalDefId, DefId>,
    erased_local_defid: HashMap<LocalDefId, Option<Erasure<'tcx>>>,
    erasures_to_check: IndexMap<LocalDefId, Erasure<'tcx>>,
    coma_names: ComaNames,
    params_open_inv: HashMap<DefId, DenseBitSet<usize>>,
    laws: OnceMap<DefId, Vec<DefId>>,
    fmir_body: OnceMap<BodyId, Box<fmir::Body<'tcx>>>,
    terms: OnceMap<DefId, Box<Option<ScopedTerm<'tcx>>>>,
    trait_impl: OnceMap<DefId, Vec<Refinement<'tcx>>>,
    sig: OnceMap<DefId, Box<PreSignature<'tcx>>>,
    opacity: OnceMap<DefId, Box<Opacity>>,
    renamer: RefCell<HashMap<HirId, Ident>>,
    pub corenamer: RefCell<HashMap<Ident, HirId>>,
    crate_name: OnceCell<why3::Symbol>,
    inhabited_ty: RefCell<HashMap<Ty<'tcx>, bool>>,
    nonzero_sized_ty: RefCell<HashMap<Ty<'tcx>, bool>>,
}

impl<'tcx> Deref for TranslationCtx<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

pub(crate) fn gather_params_open_inv(tcx: TyCtxt) -> HashMap<DefId, DenseBitSet<usize>> {
    struct VisitFns<'tcx, 'a>(
        TyCtxt<'tcx>,
        HashMap<DefId, DenseBitSet<usize>>,
        &'a ResolverAstLowering,
    );
    impl<'a> Visitor<'a> for VisitFns<'_, 'a> {
        fn visit_fn(&mut self, fk: FnKind<'a>, _: &AttrVec, _: Span, node: NodeId) {
            let (shift, decl) = match fk {
                FnKind::Fn(_, _, Fn { sig: FnSig { decl, .. }, .. }) => (0, decl),
                FnKind::Closure(_, _, decl, _) => (1, decl),
            };
            let mut open_inv_params = DenseBitSet::new_empty(shift + decl.inputs.len());
            for (i, p) in (shift..).zip(decl.inputs.iter()) {
                if is_open_inv_param(self.0, p) {
                    open_inv_params.insert(i);
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
        params_open_inv: HashMap<DefId, DenseBitSet<usize>>,
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
            terms: Default::default(),
            creusot_items,
            variant_calls: RefCell::new(IndexMap::new()),
            opts,
            erasure_required: Default::default(),
            extern_specs: Default::default(),
            extern_spec_items: Default::default(),
            erased_local_defid: Default::default(),
            erasures_to_check: Default::default(),
            coma_names: ComaNames::new(tcx),
            fmir_body: Default::default(),
            trait_impl: Default::default(),
            sig: Default::default(),
            opacity: Default::default(),
            params_open_inv,
            renamer: Default::default(),
            corenamer: Default::default(),
            crate_name: Default::default(),
            nonzero_sized_ty: Default::default(),
            inhabited_ty: Default::default(),
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

    pub(crate) fn thir_body(&self, def_id: LocalDefId) -> ThirExpr<'tcx> {
        self.tcx.thir_body(def_id).unwrap_or_else(|err| err.raise_fatal())
    }

    pub(crate) fn erased_thir(&self, def_id: DefId) -> Option<&AnfBlock<'tcx>> {
        self.erasure_required.borrow_mut().insert(def_id);
        self.externs.erased_thir(def_id)
    }

    pub(crate) fn trait_impl(&self, item: DefId) -> &[Refinement<'tcx>] {
        self.trait_impl.insert(item, |&item| self.translate_impl(item))
    }

    pub(crate) fn fmir_body(&self, item: BodyId) -> &fmir::Body<'tcx> {
        self.fmir_body.insert(item, |&item| Box::new(translation::function::fmir(self, item)))
    }

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
                    let (bound, term) = match pearlite::from_thir(self, local_id) {
                        Ok(t) => t,
                        Err(err) => err.raise_fatal(),
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

    pub(crate) fn params_open_inv(&self, def_id: DefId) -> Option<&DenseBitSet<usize>> {
        if !def_id.is_local() {
            return self.externs.params_open_inv(def_id);
        }
        self.params_open_inv.get(&def_id)
    }

    pub(crate) fn sig(&self, item: DefId) -> &PreSignature<'tcx> {
        self.sig.insert(item, |&item| Box::new(pre_sig_of(self, item)))
    }

    pub(crate) fn body_with_facts(&self, def_id: LocalDefId) -> &BodyWithBorrowckFacts<'tcx> {
        callbacks::get_body(self.tcx, def_id)
    }

    pub(crate) fn resolve(
        &self,
        scope: DefId,
        typing_env: TypingEnv<'tcx>,
        term: Term<'tcx>,
    ) -> Term<'tcx> {
        // Optimization: if we know resolve is trivial, then we do not emit a resolve
        if is_resolve_trivial(self, scope, typing_env, term.ty, term.span) {
            return Term::true_(self.tcx);
        }

        let subst = self.mk_args(&[GenericArg::from(term.ty)]);
        Term::call_no_normalize(self.tcx, Intrinsic::Resolve.get(self), subst, [term])
    }

    pub(crate) fn laws(&self, item: DefId) -> &[DefId] {
        self.laws.insert(item, |&item| self.laws_inner(item))
    }

    // TODO Make private
    pub(crate) fn extern_spec(&self, def_id: DefId) -> Option<&ExternSpec<'tcx>> {
        self.extern_specs.get(&def_id).or_else(|| self.externs.extern_spec(def_id))
    }

    pub(crate) fn opacity(&self, item: DefId) -> &Opacity {
        self.opacity.insert(item, |&item| Box::new(self.mk_opacity(item)))
    }

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
        self.tcx
            .hir_body_owners()
            .filter_map(|local_id| {
                let thir = self.thir_body(local_id);
                if erasure_required.contains(&local_id) {
                    let erasure = crate::validate::a_normal_form_for_export(self, local_id, thir)?;
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
            normalize_param_env_or_error(self.tcx, res, ObligationCause::dummy())
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

        for def_id in self.tcx.hir_body_owners() {
            let thir = self.tcx.thir_body(def_id).unwrap_or_else(|err| err.raise_fatal());
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
        for def_id in self.tcx.hir_body_owners() {
            let thir = self.tcx.thir_body(def_id).unwrap_or_else(|err| err.raise_fatal());
            let Some((eraser, erasure, to_check)) = extract_erasure_from_item(self, def_id, thir)
            else {
                continue;
            };
            self.erased_local_defid.insert(eraser, erasure);
            if let Some(to_check) = to_check {
                self.erasures_to_check.insert(eraser, to_check);
            }
        }
        if self.erasures_to_check.is_empty() {
            return;
        }
        for def_id in self.tcx.hir_body_owners() {
            if let Some(erasure) = extract_erasure_from_child(self, def_id) {
                self.erased_local_defid.insert(def_id, Some(erasure.clone()));
                self.erasures_to_check.insert(def_id, erasure);
            }
        }
    }

    pub(crate) fn iter_erasures_to_check(
        &self,
    ) -> impl Iterator<Item = (&LocalDefId, &Erasure<'tcx>)> {
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
            let r = Ident::fresh(self.crate_name(), {
                lowercase_prefix("v_", self.hir_name(ident).as_str())
            });
            self.corenamer.borrow_mut().insert(r, ident);
            r
        })
    }

    pub(crate) fn module_path(&self, id: DefId) -> ModulePath {
        self.coma_names.get(self.tcx, id)
    }

    pub(crate) fn crate_name(&self) -> why3::Symbol {
        *self.crate_name.get_or_init(|| crate_name(self.tcx))
    }

    pub(crate) fn erasure(&self, def_id: DefId) -> Option<&Option<Erasure<'tcx>>> {
        match def_id.as_local() {
            Some(local) => self.erased_local_defid.get(&local),
            None => self.externs.erasure(def_id),
        }
    }

    pub(crate) fn erasure_to_check(&self, def_id: LocalDefId) -> Option<&Erasure<'tcx>> {
        self.erasures_to_check.get(&def_id)
    }

    /// If `true`, the type is definitely non-zero sized. This is a best-effort underapproximation.
    pub fn is_nonzero_sized(&self, ty: Ty<'tcx>) -> bool {
        is_nonzero_sized(
            self.tcx,
            &mut self.nonzero_sized_ty.borrow_mut(),
            &mut self.inhabited_ty.borrow_mut(),
            ty,
        )
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

/// If `true`, the type is definitely non-zero sized. This is a best-effort underapproximation.
fn is_nonzero_sized<'tcx>(
    tcx: TyCtxt<'tcx>,
    nonzero_sized_cache: &mut HashMap<Ty<'tcx>, bool>,
    inhabited_cache: &mut HashMap<Ty<'tcx>, bool>,
    ty: Ty<'tcx>,
) -> bool {
    if let Some(&b) = nonzero_sized_cache.get(&ty) {
        return b;
    }
    use rustc_type_ir::TyKind::*;
    let b = match ty.kind() {
        Bool | Char | Int(_) | Uint(_) | Float(_) | Ref(_, _, _) | RawPtr(_, _) => true,
        Adt(def, args) => {
            def.is_box()
                || is_nonzero_sized_adt(tcx, nonzero_sized_cache, inhabited_cache, def, args)
        }
        Tuple(tys) => {
            tys.iter().any(|ty| is_nonzero_sized(tcx, nonzero_sized_cache, inhabited_cache, ty))
                && tys.iter().all(|ty| is_inhabited(tcx, inhabited_cache, ty))
        }
        Array(ty, len) => {
            is_nonzero_const(tcx, *len)
                && is_nonzero_sized(tcx, nonzero_sized_cache, inhabited_cache, *ty)
        }
        _ => false,
    };
    nonzero_sized_cache.insert(ty, b);
    b
}

/// If `true`, the constant is definitely non-zero. This is a best-effort underapproximation.
fn is_nonzero_const<'tcx>(tcx: TyCtxt<'tcx>, len: ty::Const<'tcx>) -> bool {
    match len.kind() {
        ty::ConstKind::Value(v) => v.try_to_target_usize(tcx).iter().any(|size| *size != 0),
        _ => false,
    }
}

/// Determining whether a user-defined type is zero-sized is tricky because
/// Rust makes very few guarantees about layout. For example, the compiler
/// is free to omit constructors if it can determine that they are uninhabited.
/// We use heuristics to find cases where some bits are definitely needed to
/// represent this type.
///
/// A `struct` or `enum` is non-zero sized if either:
/// - there are two inhabited constructors;
/// - there is one inhabited constructor with at least one non-zero sized field.
fn is_nonzero_sized_adt<'tcx>(
    tcx: TyCtxt<'tcx>,
    nonzero_sized_cache: &mut HashMap<Ty<'tcx>, bool>,
    inhabited_cache: &mut HashMap<Ty<'tcx>, bool>,
    def: &ty::AdtDef<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> bool {
    use rustc_type_ir::inherent::AdtDef;
    if def.is_struct() || def.is_enum() {
        let inhabiteds = def
            .variants()
            .into_iter()
            .filter(|variant| {
                variant.fields.iter().all(|field| {
                    is_inhabited(
                        tcx,
                        inhabited_cache,
                        tcx.type_of(field.did).instantiate(tcx, args),
                    )
                })
            })
            .collect::<Vec<_>>();
        inhabiteds.len() >= 2
            || inhabiteds.into_iter().any(|variant| {
                variant.fields.iter().any(|field| {
                    is_nonzero_sized(
                        tcx,
                        nonzero_sized_cache,
                        inhabited_cache,
                        tcx.type_of(field.did).instantiate(tcx, args),
                    )
                })
            })
    } else if def.is_union() {
        def.all_field_tys(tcx)
            .iter_instantiated(tcx, args)
            .any(|ty| is_nonzero_sized(tcx, nonzero_sized_cache, inhabited_cache, ty))
    } else {
        false
    }
}

/// If `true`, the type is definitely inhabited. This is a best-effort underapproximation.
fn is_inhabited<'tcx>(
    tcx: TyCtxt<'tcx>,
    inhabited_cache: &mut HashMap<Ty<'tcx>, bool>,
    ty: Ty<'tcx>,
) -> bool {
    if let Some(&b) = inhabited_cache.get(&ty) {
        return b;
    }
    let b = is_inhabited_(tcx, inhabited_cache, &mut Vec::new(), ty);
    inhabited_cache.insert(ty, b);
    b
}

// See `is_inhabited_adt` for the handling of recursive types with `visited`.
fn is_inhabited_<'tcx>(
    tcx: TyCtxt<'tcx>,
    inhabited_cache: &HashMap<Ty<'tcx>, bool>,
    visited: &mut Vec<ty::AdtDef<'tcx>>,
    ty: Ty<'tcx>,
) -> bool {
    use rustc_type_ir::TyKind::*;
    match ty.kind() {
        Bool | Char | Int(_) | Uint(_) | Float(_) | RawPtr(_, _) | Str | Slice(_) => true,
        Ref(_, ty, _) => is_inhabited_(tcx, inhabited_cache, visited, *ty),
        Adt(def, args) if def.is_box() => {
            is_inhabited_(tcx, inhabited_cache, visited, args.type_at(0))
        }
        Adt(def, args) => is_inhabited_adt(tcx, inhabited_cache, visited, *def, args),
        Tuple(tys) => tys.iter().all(|ty| is_inhabited_(tcx, inhabited_cache, visited, ty)),
        // [T; 0] is also inhabited but who needs to know that? Make a PR if you do!
        Array(ty, _) => is_inhabited_(tcx, inhabited_cache, visited, *ty),
        _ => false,
    }
}

// To handle recursive types, we keep track of ADTs we've already seen and return `false` if we re-encounter one.
// Since we may return `false` for types which end up being inhabited, we do not modify the cache during this process.
fn is_inhabited_adt<'tcx>(
    tcx: TyCtxt<'tcx>,
    inhabited_cache: &HashMap<Ty<'tcx>, bool>,
    visited: &mut Vec<ty::AdtDef<'tcx>>,
    def: ty::AdtDef<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> bool {
    if visited.contains(&def) {
        return false;
    }
    visited.push(def);
    let inhabited = if def.is_struct() || def.is_enum() {
        def.variants().into_iter().any(|variant| {
            variant.fields.iter().all(|field| {
                is_inhabited_(
                    tcx,
                    inhabited_cache,
                    visited,
                    tcx.type_of(field.did).instantiate(tcx, args),
                )
            })
        })
    } else if def.is_union() {
        use rustc_type_ir::inherent::AdtDef as _;
        def.all_field_tys(tcx)
            .iter_instantiated(tcx, args)
            .any(|ty| is_inhabited_(tcx, inhabited_cache, visited, ty))
    } else {
        false
    };
    visited.pop();
    inhabited
}
