mod borrows;
mod liveness_no_drop;
mod not_final_places;
mod resolve;

use std::{
    collections::{HashMap, HashSet},
    iter,
};

use borrows::*;
use liveness_no_drop::*;
use not_final_places::NotFinalPlaces;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_borrowck::consumers::{BodyWithBorrowckFacts, TwoPhaseActivation};
use rustc_hir::{
    HirId,
    def_id::{DefId, LocalDefId},
};
use rustc_index::{Idx as _, bit_set::MixedBitSet};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    mir::{self, BasicBlock, Local, Location, Place, traversal},
    ty::{self, TyCtxt, TypingEnv},
};
use rustc_mir_dataflow::{
    Analysis as _, ResultsCursor,
    impls::MaybeUninitializedPlaces,
    move_paths::{HasMoveData, LookupResult, MoveData, MovePathIndex},
    on_all_children_bits,
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::Symbol;
use rustc_type_ir::TyKind;
use why3::Ident;

use crate::{
    analysis::resolve::{HasMoveDataExt as _, Resolver, place_contains_borrow_deref},
    callbacks,
    contracts_items::{is_snapshot_closure, is_spec},
    ctx::{HasTyCtxt, TranslationCtx},
    extended_location::ExtendedLocation,
    gather_spec_closures::{
        InvariantsAndVariants, SpecClosures, corrected_invariant_names_and_locations,
    },
    naming::variable_name,
    translation::{
        fmir::{self, BorrowKind},
        function::discriminator_for_switch,
        pearlite::{self, Term},
    },
};

type Resolves<'tcx> = Vec<Place<'tcx>>;
type BorrowId = usize;

/// Information computed by this analysis.
#[derive(TyEncodable, TyDecodable, Clone, Debug)]
pub struct BorrowData<'tcx> {
    /// Resolves before each statement and terminator
    ///
    /// For `Call` terminators, they are split in a `Call` statement and a `Goto` terminator,
    /// each corresponding to an entry in `resolved_at`.
    /// The `Location` of the original MIR `Call` terminator becomes the `Location` of the FMIR
    /// `Call` statement, and the successor `Location` is the FMIR `Goto` terminator.
    resolved_at: HashMap<Orphan<Location>, Resolves<'tcx>>,
    resolved_between_blocks: HashMap<BasicBlock, HashMap<BasicBlock, Resolves<'tcx>>>,
    /// Locations where final borrows are created.
    final_borrows: HashMap<Orphan<Location>, BorrowId>,
    /// Locations where two-phase borrows are created.
    /// We will use this to delay the creation of two-phase borrows in our translation.
    two_phase_created: HashSet<Orphan<Location>>,
    /// Locations where two-phase borrows are activated, with the lhs, rhs of the borrow assignment, and whether the borrow is final
    two_phase_activated: HashMap<Orphan<Location>, Vec<(Place<'tcx>, Place<'tcx>, BorrowKind)>>,
}

impl<'tcx> BorrowData<'tcx> {
    pub fn new() -> Self {
        BorrowData {
            resolved_at: HashMap::new(),
            resolved_between_blocks: HashMap::new(),
            two_phase_created: HashSet::new(),
            two_phase_activated: HashMap::new(),
            final_borrows: HashMap::new(),
        }
    }

    pub(crate) fn remove_resolved_between_blocks(
        &mut self,
        bb: BasicBlock,
    ) -> Option<HashMap<BasicBlock, Resolves<'tcx>>> {
        self.resolved_between_blocks.remove(&bb)
    }

    pub(crate) fn remove_resolved_places_at(&mut self, loc: Location) -> Vec<Place<'tcx>> {
        self.resolved_at.remove(&Orphan(loc)).unwrap_or(vec![])
    }

    fn insert_final_borrow(&mut self, loc: Location, borrow_id: usize) {
        self.final_borrows.insert(Orphan(loc), borrow_id);
    }

    pub(crate) fn is_final_at(&self, loc: Location) -> fmir::BorrowKind {
        self.final_borrows
            .get(&Orphan(loc))
            .copied()
            .map_or(fmir::BorrowKind::Mut, fmir::BorrowKind::Final)
    }

    pub(crate) fn is_two_phase_at(&self, loc: Location) -> bool {
        self.two_phase_created.contains(&Orphan(loc))
    }

    pub(crate) fn remove_two_phase_activated_at(
        &mut self,
        loc: Location,
    ) -> Vec<(Place<'tcx>, Place<'tcx>, BorrowKind)> {
        self.two_phase_activated.remove(&Orphan(loc)).unwrap_or(vec![])
    }
}

/// A newtype to carry orphan trait impls.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Orphan<T>(T);

impl<D: Decoder> Decodable<D> for Orphan<Location> {
    fn decode(decoder: &mut D) -> Self {
        let block = Decodable::decode(decoder);
        let statement_index = Decodable::decode(decoder);
        Orphan(Location { block, statement_index })
    }
}

impl<E: Encoder> Encodable<E> for Orphan<Location> {
    fn encode(&self, encoder: &mut E) {
        self.0.block.encode(encoder);
        self.0.statement_index.encode(encoder);
    }
}

/// Pearlite terms that appear in a body and metadata about its variables.
pub(crate) struct BodySpecs<'tcx> {
    /// Invariants placed at the beginning of their respective loops.
    ///
    /// The string is a description for Why3.
    pub(crate) invariants: HashMap<BasicBlock, Vec<(String, Term<'tcx>)>>,
    /// Variants placed at the beginning of their respective loops.
    pub(crate) variants: HashMap<BasicBlock, Term<'tcx>>,
    /// Invariants to translate as assertions.
    pub(crate) invariant_assertions: HashMap<DefId, (Term<'tcx>, String)>,
    /// Map of the `proof_assert!` blocks to their translated version.
    pub(crate) assertions: HashMap<DefId, Term<'tcx>>,
    /// Map of the `snapshot!` blocks to their translated version.
    pub(crate) snapshots: HashMap<DefId, Term<'tcx>>,
    /// This is empty during analysis (moved into `PreAnalysisCtx`).
    pub(crate) locals: HashMap<Local, (Symbol, Ident)>,
    pub(crate) vars: fmir::LocalDecls<'tcx>,
    pub(crate) erased_locals: MixedBitSet<Local>,
}

impl<'tcx> BodySpecs<'tcx> {
    fn empty() -> Self {
        BodySpecs {
            invariants: HashMap::new(),
            variants: HashMap::new(),
            invariant_assertions: HashMap::new(),
            assertions: HashMap::new(),
            snapshots: HashMap::new(),
            locals: HashMap::new(),
            vars: fmir::LocalDecls::new(),
            erased_locals: MixedBitSet::new_empty(0),
        }
    }

    pub fn from_body(ctx: &TranslationCtx<'tcx>, body: &mir::Body<'tcx>) -> Self {
        let tcx = ctx.tcx;
        let mut erased_locals = MixedBitSet::new_empty(body.local_decls.len());
        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let ty::TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if is_spec(tcx, *def_id) || is_snapshot_closure(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });
        let (vars, locals) = translate_vars(ctx.crate_name(), body, &erased_locals);
        let InvariantsAndVariants { invariants, variants, assertions: invariant_assertions } =
            corrected_invariant_names_and_locations(ctx, body);
        let SpecClosures { assertions, snapshots } = SpecClosures::collect(ctx, body);
        BodySpecs {
            invariants,
            variants,
            invariant_assertions,
            assertions,
            snapshots,
            locals,
            vars,
            erased_locals,
        }
    }
}

/// Read-only context for `Analysis`.
/// This provides information about variables in Pearlite terms (assertions, snapshots, invariants).
pub struct AnalysisEnv<'a, 'tcx> {
    tree: fmir::ScopeTree<'tcx>,
    corenamer: &'a HashMap<Ident, HirId>,
    locals: HashMap<Local, (Symbol, Ident)>,
}

impl<'a, 'tcx> AnalysisEnv<'a, 'tcx> {
    fn new(
        tree: fmir::ScopeTree<'tcx>,
        corenamer: &'a HashMap<Ident, HirId>,
        locals: HashMap<Local, (Symbol, Ident)>,
    ) -> Self {
        AnalysisEnv { tree, corenamer, locals }
    }

    /// Construct a substitution for an inline Pearlite expression (`proof_assert`, `snapshot`).
    /// Pearlite identifiers come from HIR (`HirId`), which must correspond to places in the middle of a MIR body.
    /// The `places` argument is constructed by `ScopeTree::visible_places`.
    ///
    /// This substitution can't just be represented as a `HashMap` because at this point we don't know its keys,
    /// which are the free variables of the Pearlite expression.
    fn inline_pearlite_subst(
        &self,
        tcx: TyCtxt<'tcx>,
        scope: mir::SourceScope,
    ) -> impl Fn(Ident) -> Option<pearlite::TermKind<'tcx>> {
        let places = self.tree.visible_places(scope);
        move |ident| {
            let var = *self
                .corenamer
                .get(&ident)
                .unwrap_or_else(|| panic!("HirId not found for {:?}", ident));
            let ident2 = tcx.hir_ident(var);
            match places.get(&ident2) {
                Some(term) => Some(term.clone()),
                None => panic!("No place found for {:?}", ident2),
            }
        }
    }

    fn check_use_in_logic(
        &self,
        term: &Term<'tcx>,
        tcx: TyCtxt<'tcx>,
        move_data: &MoveData<'tcx>,
        bad_vars: &MixedBitSet<MovePathIndex>,
    ) {
        // TODO: We should refine this check to consider places and not only locals
        let free_vars = term.free_vars();
        for f in bad_vars.iter() {
            if let Some((sym, ident)) =
                move_data.move_paths[f].place.as_local().and_then(|l| self.locals.get(&l))
                && free_vars.contains(ident)
            {
                let msg = format!("Use of borrowed or uninitialized variable {}", sym.as_str());
                tcx.crash_and_error(term.span, msg);
            }
        }
    }
}

/// The main analysis struct.
pub struct Analysis<'a, 'tcx> {
    analysis_env: AnalysisEnv<'a, 'tcx>,
    resolver: Resolver<'a, 'tcx>,
    typing_env: TypingEnv<'tcx>,
    /// Places to resolve before and after the current statement
    current_resolved: Vec<Place<'tcx>>,
    not_final_places: ResultsCursor<'a, 'tcx, NotFinalPlaces<'tcx>>,
    /// `&mut` because we also rename assertions here
    body_specs: &'a mut BodySpecs<'tcx>,
    data: BorrowData<'tcx>,
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for Analysis<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.resolver.tcx()
    }
}

impl<'a, 'tcx> HasMoveData<'tcx> for Analysis<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        self.resolver.move_data()
    }
}

fn local_typing_env(tcx: TyCtxt<'_>, def_id: DefId) -> TypingEnv<'_> {
    let param_env = tcx.param_env(def_id);
    let typing_mode = ty::TypingMode::post_borrowck_analysis(tcx, def_id.as_local().unwrap());
    TypingEnv { typing_mode, param_env }
}

impl<'a, 'tcx> Analysis<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        analysis_env: AnalysisEnv<'a, 'tcx>,
        body: &'a BodyWithBorrowckFacts<'tcx>,
        body_specs: &'a mut BodySpecs<'tcx>,
        move_data: &'a MoveData<'tcx>,
    ) -> Self {
        Self {
            analysis_env,
            typing_env: local_typing_env(tcx, body.body.source.def_id()),
            resolver: Resolver::new(
                tcx,
                &body.body,
                &body.borrow_set,
                &body.region_inference_context,
                move_data,
            ),
            current_resolved: Default::default(),
            not_final_places: NotFinalPlaces::new(tcx, &body.body)
                .iterate_to_fixpoint(tcx, &body.body, None)
                .into_results_cursor(&body.body),
            data: BorrowData::new(),
            body_specs,
        }
    }

    fn body(&self) -> &mir::Body<'tcx> {
        self.resolver.body
    }

    fn resolve_before_assignment(
        &mut self,
        need: MixedBitSet<MovePathIndex>,
        resolved: &MixedBitSet<MovePathIndex>,
        loc: Location,
        destination: Place<'tcx>,
    ) {
        // The assignement may, in theory, modify a variable that needs to be resolved.
        // Hence we resolve before the assignment.
        self.resolve_places(need, resolved);

        // We resolve the destination place, if necessary
        match self.move_data().rev_lookup.find(destination.as_ref()) {
            LookupResult::Parent(None) => {
                // for the kind of move data we ask, all the locals should be move paths, so
                // we know we find something here.
                unreachable!()
            }
            LookupResult::Parent(Some(mp)) => {
                let uninit = self.resolver.uninit_places_before(loc);
                // My understanding is that if the destination is not a move path, then it has to
                // be initialized before the assignment.
                assert!(!uninit.contains(mp));
                if !resolved.contains(mp) {
                    // If destination is a reborrow, then mp cannot be in resolved (since
                    // we are writting in it), so we will go through this test.
                    // Otherwise, we resolve only if it is not already resolved.
                    self.emit_resolve(destination);
                }
            }
            LookupResult::Exact(mp) => {
                // need_before can contain mp or its children if a subplace of destination
                // is reborrowed
                let (need_before, resolved) =
                    self.resolver.need_resolve_resolved_places_at(ExtendedLocation::Mid(loc));
                let mut to_resolve = self.empty_bitset();
                on_all_children_bits(self.move_data(), mp, |mp| {
                    if need_before.contains(mp) {
                        to_resolve.insert(mp);
                    }
                });
                self.resolve_places(to_resolve, &resolved);
            }
        }
    }

    fn resolve_after_assignment(&mut self, next_loc: Location, destination: Place<'tcx>) {
        let live = self.resolver.live_places_before(next_loc);
        let (_, resolved) =
            self.resolver.need_resolve_resolved_places_at(ExtendedLocation::Start(next_loc));
        let dest = destination.as_ref();
        match self.move_data().rev_lookup.find(dest) {
            LookupResult::Parent(None) => {
                // for the kind of move data we ask, all the locals should be move paths, so
                // we know we find something here.
                unreachable!()
            }
            LookupResult::Parent(Some(mp)) => {
                if !live.contains(mp) {
                    if place_contains_borrow_deref(dest, self.body(), self.tcx()) {
                        if resolved.contains(mp) {
                            self.emit_resolve(self.move_data().move_paths[mp].place);
                        }
                    } else {
                        self.emit_resolve(destination);
                    }
                }
            }
            LookupResult::Exact(mp) => {
                let mut to_resolve = self.empty_bitset();
                on_all_children_bits(self.move_data(), mp, |imp| {
                    if !live.contains(imp) {
                        to_resolve.insert(imp);
                    }
                });
                self.resolve_places(to_resolve, &resolved);
            }
        }
    }

    fn emit_resolve(&mut self, pl: Place<'tcx>) {
        self.current_resolved.push(pl);
    }

    /// We try to coalesce resolutions for places, if possible
    /// TODO: We may actually want to do the opposite: resolve as deeply as possible,
    /// but taking care of type opacity and recursive types.
    fn resolve_places(
        &mut self,
        to_resolve: MixedBitSet<MovePathIndex>,
        resolved: &MixedBitSet<MovePathIndex>,
    ) {
        let mut to_resolve_full = to_resolve.clone();
        for mp in to_resolve.iter() {
            let mut all_children = true;
            on_all_children_bits(self.move_data(), mp, |imp| {
                if !to_resolve.contains(imp) && !resolved.contains(imp) {
                    all_children = false
                }
            });
            if all_children {
                on_all_children_bits(self.move_data(), mp, |imp| {
                    if mp != imp {
                        to_resolve_full.remove(imp);
                    }
                });
            } else {
                to_resolve_full.remove(mp);
            }
        }

        let mut to_resolve_partial = to_resolve;
        let mut v = vec![];
        for mp in to_resolve_full.iter() {
            on_all_children_bits(self.move_data(), mp, |imp| {
                to_resolve_partial.remove(imp);
            });

            let pl = self.move_data().move_paths[mp].place;
            if !self.body_specs.erased_locals.contains(pl.local) {
                v.push(pl);
            }
        }

        for mp in to_resolve_partial.iter() {
            let pl = self.move_data().move_paths[mp].place;
            if self.body_specs.erased_locals.contains(pl.local) {
                continue;
            }
            let local_decls = &self.body().local_decls;
            let ty = pl.ty(local_decls, self.tcx());
            let ty = self.tcx().normalize_erasing_regions(self.typing_env, ty);
            let mut insert = |pl: Place<'tcx>| {
                if !matches!(self.move_data().rev_lookup.find(pl.as_ref()), LookupResult::Exact(_))
                {
                    v.push(pl)
                }
            };
            use TyKind::*;
            match ty.ty.kind() {
                Adt(adt_def, subst) => {
                    if adt_def.is_box() {
                        insert(self.tcx().mk_place_deref(pl));
                    } else if adt_def.is_enum() {
                        if let Some(vid) = ty.variant_index {
                            let var = adt_def.variant(vid);
                            // TODO: honor access rights for these fields.
                            // I.e., we should not resolve private fields.
                            // Problem: it's unclear what to do if we need to resolve a private
                            // field, but not the whole struct/enum
                            for (fi, fd) in var.fields.iter_enumerated() {
                                insert(self.tcx().mk_place_field(pl, fi, fd.ty(self.tcx(), subst)));
                            }
                        } else {
                            for (i, _var) in adt_def.variants().iter().enumerate() {
                                insert(self.tcx().mk_place_downcast(
                                    pl,
                                    *adt_def,
                                    VariantIdx::new(i),
                                ))
                            }
                        }
                    } else {
                        // TODO: idem
                        for (fi, fd) in adt_def.non_enum_variant().fields.iter_enumerated() {
                            insert(self.tcx().mk_place_field(pl, fi, fd.ty(self.tcx(), subst)));
                        }
                    }
                }

                Tuple(tys) => {
                    for (i, ty) in tys.iter().enumerate() {
                        insert(self.tcx().mk_place_field(pl, FieldIdx::new(i), ty));
                    }
                }

                Closure(_did, substs) => {
                    for (i, ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                        insert(self.tcx().mk_place_field(pl, FieldIdx::new(i), ty));
                    }
                }

                Array(_, _) | Slice(_) | Pat(_, _) => {
                    self.span_bug(
                        local_decls[pl.local].source_info.span,
                        format!("Unsupported type during resolution: {}", ty.ty),
                    );
                }

                Bool
                | Char
                | Int(_)
                | Uint(_)
                | Float(_)
                | Foreign(_)
                | Str
                | RawPtr(_, _)
                | Alias(_, _)
                | Param(_)
                | Bound(_, _)
                | Placeholder(_)
                | Infer(_)
                | Error(_)
                | Ref(_, _, _)
                | FnDef(_, _)
                | FnPtr(..)
                | Dynamic(_, _, _)
                | CoroutineClosure(_, _)
                | Coroutine(_, _)
                | CoroutineWitness(_, _)
                | Never
                | UnsafeBinder(_) => unreachable!("{}", ty.ty),
            }
        }

        // TODO determine resolution order based on outlives relation?
        v.sort_by_key(|pl| pl.local);
        for pl in v.into_iter().rev() {
            self.emit_resolve(pl);
        }
    }

    fn resolve_places_between_blocks(&mut self, bb: BasicBlock) {
        let pred_blocks = &self.resolver.body.basic_blocks.predecessors()[bb];
        if pred_blocks.is_empty() {
            return;
        }
        let mut resolved_between = pred_blocks
            .iter()
            .map(|&pred| self.resolver.resolved_places_between_blocks(pred, bb))
            .collect::<Vec<_>>();
        for (pred, resolved) in iter::zip(pred_blocks, resolved_between.iter_mut()) {
            let bbd = &self.resolver.body.basic_blocks[*pred];
            let Some(discr_pl) = discriminator_for_switch(bbd) else {
                continue;
            };
            let LookupResult::Exact(discr_mp) = self.move_data().rev_lookup.find(discr_pl.as_ref())
            else {
                continue;
            };
            let Some(adt) = discr_pl.ty(self.resolver.body, self.tcx()).ty.ty_adt_def() else {
                continue;
            };
            let mir::TerminatorKind::SwitchInt { targets, .. } = &bbd.terminator().kind else {
                unreachable!()
            };
            if targets.otherwise() == bb {
                continue;
            }
            let mut inactive_mps = self.empty_bitset();
            // We first insert all the move paths of the discriminator..
            on_all_children_bits(self.move_data(), discr_mp, |mpi| {
                inactive_mps.insert(mpi);
            });
            // ..and then remove everything which is active in this branch
            let mut discrs = adt.discriminants(self.tcx());
            for discr in targets.iter().filter_map(|(val, tgt)| (tgt == bb).then_some(val)) {
                let var = discrs.find(|d| d.1.val == discr).unwrap().0;
                let pl = self.tcx().mk_place_downcast(discr_pl, adt, var);
                if let LookupResult::Exact(mp) = self.move_data().rev_lookup.find(pl.as_ref()) {
                    on_all_children_bits(self.move_data(), mp, |mpi| {
                        inactive_mps.remove(mpi);
                    })
                } else {
                    inactive_mps.remove(discr_mp);
                }
            }
            resolved.0.subtract(&inactive_mps);
        }
        // If we have multiple predecessors (join point) but all of them agree on the deaths, then don't introduce a dedicated block.
        if resolved_between.windows(2).all(|r| r[0] == r[1]) {
            let r = resolved_between.into_iter().next().unwrap();
            self.resolve_places(r.0, &r.1);
            return;
        }
        for (pred, resolved) in iter::zip(pred_blocks, resolved_between) {
            // If no resolves occured in block transition then skip entirely
            if resolved.0.is_empty() {
                continue;
            };
            // Otherwise, we emit the resolves and move them to a standalone block.
            self.resolve_places(resolved.0, &resolved.1);
            let current_resolved = std::mem::take(&mut self.current_resolved);
            self.data
                .resolved_between_blocks
                .entry(*pred)
                .or_insert(HashMap::new())
                .insert(bb, current_resolved);
        }
    }

    fn store_resolved_before(&mut self, loc: Location) {
        assert!(!self.data.resolved_at.contains_key(&Orphan(loc)));
        if !self.current_resolved.is_empty() {
            let resolved = std::mem::take(&mut self.current_resolved);
            self.data.resolved_at.insert(Orphan(loc), resolved);
        }
    }

    /// Entry point of the analysis
    fn run(&mut self) {
        for (bb, bbd) in traversal::reverse_postorder(self.resolver.body) {
            if bbd.is_cleanup {
                continue;
            }
            let tcx = self.tcx();
            let mut variants_and_invariants = self
                .body_specs
                .invariants
                .get_mut(&bb)
                .into_iter()
                .flatten()
                .map(|(_, term)| term)
                .chain(self.body_specs.variants.get_mut(&bb))
                .peekable();
            if variants_and_invariants.peek().is_some() {
                let bad_vars = self.resolver.bad_vars_at(bb.start_location());
                let scope = self.resolver.body.source_info(bb.start_location()).scope;
                let subst = self.analysis_env.inline_pearlite_subst(tcx, scope);
                for term in variants_and_invariants {
                    term.subst(&subst);
                    self.analysis_env.check_use_in_logic(
                        term,
                        tcx,
                        self.resolver.move_data(),
                        &bad_vars,
                    );
                }
            }
            self.resolve_places_between_blocks(bb);
            if bb == mir::START_BLOCK {
                let (_, resolved) = self
                    .resolver
                    .need_resolve_resolved_places_at(ExtendedLocation::Start(Location::START));
                self.resolve_places(resolved.clone(), &resolved)
            }
            let mut loc = bb.start_location();
            for statement in &bbd.statements {
                self.analyze_statement(statement, loc);
                loc = loc.successor_within_block();
            }
            self.analyze_terminator(bbd.terminator(), loc);
        }
    }

    fn analyze_statement(&mut self, statement: &mir::Statement<'tcx>, loc: Location) {
        self.activate_two_phase(loc);
        use mir::StatementKind::*;
        match statement.kind {
            Assign(box (pl, ref rvalue)) => {
                let (need, resolved) =
                    self.resolver.resolved_places_during(ExtendedLocation::Mid(loc));
                self.resolve_before_assignment(need, &resolved, loc, pl);
                self.analyze_assign(rvalue, loc, statement.source_info);
                self.store_resolved_before(loc);
                self.resolve_after_assignment(loc.successor_within_block(), pl);
            }
            // All these instructions are no-ops in the dynamic semantics, but may trigger resolution
            Nop
            | StorageDead(_)
            | StorageLive(_)
            | FakeRead(_)
            | AscribeUserType(_, _)
            | Retag(_, _)
            | Coverage(_)
            | PlaceMention(_)
            | ConstEvalCounter
            | BackwardIncompatibleDropHint { .. } => {
                let (mut need, resolved) =
                    self.resolver.resolved_places_during(ExtendedLocation::End(loc));
                if let StorageDead(local) | StorageLive(local) = statement.kind {
                    // These instructions signal that a local goes out of scope. We resolve any needed
                    // move path it contains. These are typically frozen places.
                    let (need_start, _) =
                        self.resolver.need_resolve_resolved_places_at(ExtendedLocation::Start(loc));
                    for mp in need_start.clone().iter() {
                        if self.resolver.move_data().base_local(mp) == local {
                            need.insert(mp);
                        }
                    }
                }
                self.resolve_places(need, &resolved);
                self.store_resolved_before(loc);
            }
            _ => self.store_resolved_before(loc),
        }
    }

    fn analyze_assign(&mut self, rvalue: &mir::Rvalue<'tcx>, loc: Location, si: mir::SourceInfo) {
        match rvalue {
            mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, pl) => {
                if !self.is_two_phase(loc) {
                    self.check_final(pl, loc);
                }
            }
            mir::Rvalue::Aggregate(box kind, _ops) => match kind {
                mir::AggregateKind::Closure(def_id, _subst) => {
                    let tcx = self.tcx();
                    let spec = self
                        .body_specs
                        .invariant_assertions
                        .get_mut(def_id)
                        .map(|(term, _)| term)
                        .or_else(|| self.body_specs.assertions.get_mut(def_id));
                    spec.into_iter().for_each(|term| {
                        let bad_vars = self.resolver.bad_vars_at(loc);
                        let subst = self.analysis_env.inline_pearlite_subst(tcx, si.scope);
                        term.subst(&subst);
                        self.analysis_env.check_use_in_logic(
                            term,
                            tcx,
                            &self.resolver.move_data(),
                            &bad_vars,
                        );
                    })
                }
                _ => {}
            },
            _ => {}
        }
    }

    fn analyze_terminator(&mut self, terminator: &mir::Terminator<'tcx>, mut loc: Location) {
        self.activate_two_phase(loc);
        use mir::TerminatorKind::*;
        match terminator.kind {
            Return => {
                let (mut need, resolved) =
                    self.resolver.need_resolve_resolved_places_at(ExtendedLocation::Start(loc));
                // do not resolve return local
                for mp in need.clone().iter() {
                    if self.move_data().base_local(mp) == Local::from_usize(0) {
                        need.remove(mp);
                    }
                }
                self.resolve_places(need, &resolved);
            }
            Call { ref func, destination, target, fn_span, .. } => {
                let (need, resolved) =
                    self.resolver.resolved_places_during(ExtendedLocation::End(loc));
                self.resolve_before_assignment(need, &resolved, loc, destination);

                // If this is a snapshot, check that it doesn't use uninitialized or borrowed variables
                // (if this is not a snapshot, it won't be found in `self.body_specs.snapshots` so this will be a noop)
                let &TyKind::FnDef(_fun_def_id, subst) = func.ty(self.body(), self.tcx()).kind()
                else {
                    self.fatal_error(fn_span, "unsupported function call type").emit()
                };
                if let Some(ty) = subst.get(1)
                    && let ty::GenericArgKind::Type(ty) = ty.kind()
                {
                    if let ty::TyKind::Closure(def_id, _) = ty.kind() {
                        let tcx = self.tcx();
                        self.body_specs.snapshots.get_mut(def_id).into_iter().for_each(|term| {
                            let bad_vars = self.resolver.bad_vars_at(loc);
                            let subst = self
                                .analysis_env
                                .inline_pearlite_subst(tcx, terminator.source_info.scope);
                            term.subst(&subst);
                            self.analysis_env.check_use_in_logic(
                                term,
                                tcx,
                                &self.resolver.move_data(),
                                &bad_vars,
                            );
                        });
                    }
                }

                self.store_resolved_before(loc);
                loc = loc.successor_within_block();
                if let Some(_) = target {
                    self.resolve_after_assignment(target.unwrap().start_location(), destination)
                }
            }
            Drop { place, .. } => {
                // place may need to be resolved since it may be frozen.
                if let LookupResult::Exact(mp) = self.move_data().rev_lookup.find(place.as_ref()) {
                    let (need_start, resolved) =
                        self.resolver.need_resolve_resolved_places_at(ExtendedLocation::Start(loc));
                    let mut to_resolve = self.resolver.empty_bitset();
                    on_all_children_bits(self.move_data(), mp, |mpi| {
                        if need_start.contains(mpi) {
                            to_resolve.insert(mpi);
                        }
                    });
                    self.resolve_places(to_resolve, &resolved);
                }
                let (need, resolved) =
                    self.resolver.resolved_places_during(ExtendedLocation::End(loc));
                self.resolve_places(need, &resolved)
            }
            _ => {
                let (need, resolved) =
                    self.resolver.resolved_places_during(ExtendedLocation::End(loc));
                self.resolve_places(need, &resolved)
            }
        }
        self.store_resolved_before(loc);
    }

    /// Store the location if it is a two-phase borrow creation.
    fn is_two_phase(&mut self, loc: Location) -> bool {
        let borrows = self.resolver.borrow_set();
        let is_two_phase = borrows.location_map().get(&loc).iter().any(|borrow| {
            matches!(borrow.activation_location(), TwoPhaseActivation::ActivatedAt(_))
        });
        if is_two_phase {
            self.data.two_phase_created.insert(Orphan(loc));
        }
        is_two_phase
    }

    /// Collect two-phase borrows activated at this location.
    fn activate_two_phase(&mut self, loc: Location) {
        let not_final_places = &mut self.not_final_places;
        let borrows = self.resolver.borrow_set();
        let mut activations = Vec::new();
        for i in borrows.activation_map().get(&loc).iter().flat_map(|is| is.iter()) {
            let borrow = &borrows[*i];
            let borrowed = borrow.borrowed_place();
            let is_final = NotFinalPlaces::is_final_at(not_final_places, &borrowed, loc);
            activations.push((borrow.assigned_place(), borrowed, is_final))
        }
        if !activations.is_empty() {
            self.data.two_phase_activated.insert(Orphan(loc), activations);
        }
    }

    /// Remember this location if it is a final borrow.
    fn check_final(&mut self, pl: &Place<'tcx>, loc: Location) {
        let is_final = NotFinalPlaces::is_final_at(
            &mut self.not_final_places,
            pl,
            loc.successor_within_block(),
        );
        if let fmir::BorrowKind::Final(borrow_id) = is_final {
            self.data.insert_final_borrow(loc, borrow_id);
        }
    }
}

/// Analysis to run from crates that don't have access to creusot-contracts.
// TODO: this will be used very soon
#[allow(dead_code)]
pub(crate) fn run_without_specs<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> BorrowData<'tcx> {
    let body = callbacks::get_body(tcx, def_id);
    let mut body_specs = BodySpecs::empty();
    let corenamer = HashMap::new();
    let analysis_env = AnalysisEnv::new(fmir::ScopeTree::empty(), &corenamer, HashMap::new());

    let move_data = MoveData::gather_moves(&body.body, tcx, |_| true);
    let mut analysis = Analysis::new(tcx, analysis_env, &body, &mut body_specs, &move_data);
    analysis.run();
    analysis.data
}

/// Analysis to run from crates that use creusot-contracts.
pub(crate) fn run_with_specs<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &BodyWithBorrowckFacts<'tcx>,
    body_specs: &mut BodySpecs<'tcx>,
) -> BorrowData<'tcx> {
    let tcx = ctx.tcx;
    let corenamer = &ctx.corenamer.borrow();
    // We take `locals` from `body_specs` and put it back later
    let locals = std::mem::take(&mut body_specs.locals);
    let tree = fmir::ScopeTree::build(&body.body, tcx, &locals);
    let analysis_env = AnalysisEnv::new(tree, corenamer, locals);

    let move_data = MoveData::gather_moves(&body.body, tcx, |_| true);
    let mut analysis = Analysis::new(tcx, analysis_env, body, body_specs, &move_data);
    analysis.run();

    let data = analysis.data;
    let AnalysisEnv { locals, .. } = analysis.analysis_env;
    body_specs.locals = locals;
    data
}

/// Find a fmir name for each variable in `body`.
///
/// This will skip mir variables that are in `erased_locals`.
///
/// # Returns
/// - The mapping of mir locals to the symbol used in fmir.
/// - Each (unique) fmir symbol is then mapped to the [`LocalDecl`] information of the
///   mir local (the `vars` variable).
fn translate_vars<'tcx>(
    crate_name: why3::Symbol,
    body: &mir::Body<'tcx>,
    erased_locals: &MixedBitSet<Local>,
) -> (fmir::LocalDecls<'tcx>, HashMap<Local, (Symbol, Ident)>) {
    let mut vars = fmir::LocalDecls::with_capacity(body.local_decls.len());
    let mut locals = HashMap::new();
    let external_body = !body.source.def_id().is_local();

    use mir::VarDebugInfoContents::Place;

    for (loc, d) in body.local_decls.iter_enumerated() {
        if erased_locals.contains(loc) {
            continue;
        }
        // `is_user_variable` panics if the body comes from another crate
        let temp = external_body || !d.is_user_variable();
        let name = if temp {
            format!("_{}", loc.index())
        } else {
            let x = body.var_debug_info.iter().find(|var_info| match var_info.value {
                Place(p) => p.as_local().map(|l| l == loc).unwrap_or(false),
                _ => false,
            });
            let debug_info = x.expect("expected user variable to have name");
            variable_name(debug_info.name.as_str())
        };
        let ident = Ident::fresh(crate_name, &name);
        locals.insert(loc, (Symbol::intern(&name), ident));
        let is_arg = 0 < loc.index() && loc.index() <= body.arg_count;
        vars.insert(
            ident,
            fmir::LocalDecl { span: d.source_info.span, ty: d.ty, temp, arg: is_arg },
        );
    }
    (vars, locals)
}

#[allow(dead_code)]
pub fn debug<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) {
    let move_data = MoveData::gather_moves(body, tcx, |_| true);

    let mut uninit = MaybeUninitializedPlaces::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    let mut uninit2 = MaybeUninitializedPlaces::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    let mut live = MaybeLiveExceptDrop::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    let mut live2 = MaybeLiveExceptDrop::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    for (bb, bbd) in traversal::preorder(body) {
        if bbd.is_cleanup {
            continue;
        }
        println!("{:?}", bb);
        let mut loc = bb.start_location();
        for statement in &bbd.statements {
            uninit.seek_before_primary_effect(loc);
            uninit2.seek_after_primary_effect(loc);
            live.seek_before_primary_effect(loc);
            live2.seek_after_primary_effect(loc);

            println!(
                "{:<45} uninit={:?} -> {:?} live={:?} <- {:?}",
                format!("{:?}", statement),
                uninit.get().iter().collect::<Vec<_>>(),
                uninit2.get().iter().collect::<Vec<_>>(),
                live.get().iter().collect::<Vec<_>>(),
                live2.get().iter().collect::<Vec<_>>(),
            );
            loc = loc.successor_within_block();
        }

        uninit.seek_before_primary_effect(loc);
        uninit2.seek_after_primary_effect(loc);
        live.seek_before_primary_effect(loc);
        live2.seek_after_primary_effect(loc);

        println!(
            "{:<45} uninit={:?} -> {:?} live={:?} <- {:?}",
            format!("{:?}", bbd.terminator().kind),
            uninit.get().iter().collect::<Vec<_>>(),
            uninit2.get().iter().collect::<Vec<_>>(),
            live.get().iter().collect::<Vec<_>>(),
            live2.get().iter().collect::<Vec<_>>(),
        );
    }
}
