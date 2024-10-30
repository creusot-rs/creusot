use std::{collections::HashMap, ops::Deref};

pub(crate) use crate::backend::clone_map::*;
use crate::{
    attributes::{
        gather_params_open_inv, is_extern_spec, is_logic, is_predicate, is_prophetic,
        opacity_witness_name,
    },
    backend::{ty::ty_binding_group, ty_inv::is_tyinv_trivial},
    callbacks,
    creusot_items::{self, CreusotItems},
    error::CreusotResult,
    metadata::{BinaryMetadata, Metadata},
    options::Options,
    specification::{pre_sig_of, PreSignature},
    translation::{
        self,
        external::{extract_extern_specs_from_item, ExternSpec},
        fmir,
        function::ClosureContract,
        pearlite::{self, Term},
        specification::ContractClauses,
        traits::TraitImpl,
    },
    util::{erased_identity_for_item, parent_module},
};
use indexmap::{IndexMap, IndexSet};
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_errors::{Diag, FatalAbort};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{Body, Promoted, TerminatorKind},
    ty::{Clause, GenericArg, GenericArgsRef, ParamEnv, Predicate, Ty, TyCtxt, Visibility},
};
use rustc_span::{Span, Symbol};

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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemType {
    Logic { prophetic: bool },
    Predicate { prophetic: bool },
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
    pub(crate) fn to_str(&self) -> &str {
        match self {
            ItemType::Logic { prophetic: false } => "logic function",
            ItemType::Logic { prophetic: true } => "prophetic logic function",
            ItemType::Predicate { prophetic: false } => "predicate",
            ItemType::Predicate { prophetic: true } => "prophetic predicate",
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
            (ItemType::Predicate { prophetic: false }, ItemType::Predicate { prophetic: true }) => {
                true
            }
            _ => self == trait_type,
        }
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
    closure_contract: HashMap<DefId, ClosureContract<'tcx>>,
    params_open_inv: HashMap<DefId, Vec<usize>>,
}

impl<'tcx> Deref for TranslationCtx<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

impl<'tcx, 'sess> TranslationCtx<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, opts: Options) -> Self {
        let params_open_inv = gather_params_open_inv(tcx);
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
            closure_contract: Default::default(),
            params_open_inv,
        }
    }

    pub(crate) fn load_metadata(&mut self) {
        self.externs.load(self.tcx, &self.opts.extern_paths);
    }

    queryish!(trait_impl, &TraitImpl<'tcx>, translate_impl);

    queryish!(closure_contract, &ClosureContract<'tcx>, build_closure_contract);

    pub(crate) fn fmir_body(&mut self, body_id: BodyId) -> &fmir::Body<'tcx> {
        if !self.fmir_body.contains_key(&body_id) {
            let fmir = translation::function::fmir(self, body_id);
            self.fmir_body.insert(body_id, fmir);
        }
        self.fmir_body.get(&body_id).unwrap()
    }

    pub(crate) fn term(&mut self, def_id: DefId) -> Option<&Term<'tcx>> {
        if !def_id.is_local() {
            return self.externs.term(def_id);
        }

        if self.has_body(def_id) {
            if !self.terms.contains_key(&def_id) {
                let mut term = pearlite::pearlite(self, def_id.expect_local())
                    .unwrap_or_else(|e| e.emit(self.tcx));
                pearlite::normalize(self.tcx, self.param_env(def_id), &mut term);

                self.terms.insert(def_id, term);
            };
            self.terms.get(&def_id)
        } else {
            None
        }
    }

    pub(crate) fn params_open_inv(&self, def_id: DefId) -> Option<&Vec<usize>> {
        if !def_id.is_local() {
            return self.externs.params_open_inv(def_id);
        }
        self.params_open_inv.get(&def_id)
    }

    queryish!(sig, &PreSignature<'tcx>, |ctx: &mut Self, key| {
        let mut pre_sig = pre_sig_of(&mut *ctx, key);
        pre_sig = pre_sig.normalize(ctx.tcx, ctx.param_env(key));
        pre_sig
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
            let mut body = callbacks::get_body(self.tcx, def_id)
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

            self.bodies.insert(def_id, body);
        };

        self.bodies.get(&def_id).unwrap()
    }

    pub(crate) fn type_invariant(
        &self,
        param_env: ParamEnv<'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        let ty = self.try_normalize_erasing_regions(param_env, ty).ok()?;

        if is_tyinv_trivial(self.tcx, param_env, ty) {
            None
        } else {
            let inv_did =
                self.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
            let substs = self.mk_args(&[GenericArg::from(ty)]);
            Some((inv_did, substs))
        }
    }

    pub(crate) fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        // TODO: try to add a code back in
        self.tcx.dcx().span_fatal(span, msg.to_string())
    }

    pub(crate) fn fatal_error(&self, span: Span, msg: &str) -> Diag<'tcx, FatalAbort> {
        // TODO: try to add a code back in
        self.tcx.dcx().struct_span_fatal(span, msg.to_string())
    }

    pub(crate) fn error(&self, span: Span, msg: &str) -> Diag<'tcx, rustc_errors::ErrorGuaranteed> {
        self.tcx.dcx().struct_span_err(span, msg.to_string())
    }

    pub(crate) fn warn(&self, span: Span, msg: &str) -> Diag<'tcx, ()> {
        self.tcx.dcx().struct_span_warn(span, msg.to_string())
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
        if !matches!(self.item_type(item), ItemType::Predicate { .. } | ItemType::Logic { .. }) {
            return Opacity(Visibility::Public);
        };

        let witness = opacity_witness_name(self.tcx, item)
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
        BinaryMetadata::from_parts(
            &self.terms,
            &self.creusot_items,
            &self.extern_specs,
            &self.params_open_inv,
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
            .unwrap_or_else(|| (def_id, erased_identity_for_item(self.tcx, def_id)));
        if let Some(es) = self.extern_spec(id) {
            let base_predicates =
                self.tcx.param_env(def_id).caller_bounds().into_iter().map(Clause::as_predicate);
            let additional_predicates = es.predicates_for(self.tcx, subst).into_iter();
            let clauses = base_predicates
                .chain(additional_predicates)
                .map(Predicate::expect_clause)
                .collect::<Vec<_>>();
            let res =
                ParamEnv::new(self.mk_clauses(&clauses), rustc_infer::traits::Reveal::UserFacing);
            // FIXME: param envs should be normalized (this is an invariant of the trait solver),
            // but calling this function here causes an overflow in the handling of PartialEq::eq
            // I see two solutions:
            //    1- Wait for the next trait solver that does not need this (I think).
            //    2- Allow adding new generic type variables in extern specs, so that we could write
            //             Self: DeepModel<DeepModelTy = T>,
            //             Rhs: DeepModel<DeepModelTy = T>;
            //
            // let res = normalize_param_env_or_error(self.tcx, res, ObligationCause::dummy());
            res
        } else {
            self.tcx.param_env(def_id)
        }
    }

    pub(crate) fn has_body(&mut self, def_id: DefId) -> bool {
        if let Some(local_id) = def_id.as_local() {
            self.tcx.hir().maybe_body_owned_by(local_id).is_some()
        } else {
            match self.item_type(def_id) {
                ItemType::Logic { .. } | ItemType::Predicate { .. } => self.term(def_id).is_some(),
                _ => false,
            }
        }
    }

    pub(crate) fn load_extern_specs(&mut self) -> CreusotResult<()> {
        let mut traits_or_impls = Vec::new();

        for def_id in self.tcx.hir().body_owners() {
            if is_extern_spec(self.tcx, def_id.to_def_id()) {
                if let Some(container) = self.opt_associated_item(def_id.to_def_id()) {
                    traits_or_impls.push(container.def_id)
                }

                let (i, es) = extract_extern_specs_from_item(self, def_id)?;
                let c = es.contract.clone();

                if self.extern_spec(i).is_some() {
                    self.crash_and_error(
                        self.def_span(def_id),
                        &format!("duplicate extern specification for {i:?}"),
                    );
                };

                let _ = self.extern_specs.insert(i, es);

                self.extern_spec_items.insert(def_id, i);

                for id in c.iter_ids() {
                    self.term(id).unwrap();
                }
            }
        }

        // Force extern spec items to get loaded so we export them properly
        let need_to_load: Vec<_> =
            self.extern_specs.values().flat_map(|e| e.contract.iter_ids()).collect();

        for id in need_to_load {
            self.term(id);
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
                    arg_subst: Vec::new(),
                    additional_predicates,
                },
            );
        }

        Ok(())
    }

    pub(crate) fn item_type(&self, def_id: DefId) -> ItemType {
        match self.tcx.def_kind(def_id) {
            DefKind::Trait => ItemType::Trait,
            DefKind::Impl { .. } => ItemType::Impl,
            DefKind::Fn | DefKind::AssocFn => {
                if is_predicate(self.tcx, def_id) {
                    ItemType::Predicate { prophetic: is_prophetic(self.tcx, def_id) }
                } else if is_logic(self.tcx, def_id) {
                    ItemType::Logic { prophetic: is_prophetic(self.tcx, def_id) }
                } else {
                    ItemType::Program
                }
            }
            DefKind::AssocConst | DefKind::Const => ItemType::Constant,
            DefKind::Closure => ItemType::Closure,
            DefKind::Struct | DefKind::Enum | DefKind::Union => ItemType::Type,
            DefKind::AssocTy => ItemType::AssocTy,
            DefKind::Field => ItemType::Field,
            DefKind::AnonConst => panic!(),
            DefKind::Variant => ItemType::Variant,
            dk => ItemType::Unsupported(dk),
        }
    }
}
