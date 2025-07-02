use std::{
    collections::{HashMap, HashSet},
    iter,
};

use crate::{
    analysis::{Borrows, MaybeLiveExceptDrop, NotFinalPlaces}, contracts_items::{is_snapshot_closure, is_spec}, ctx::{body_with_facts, TranslationCtx}, gather_spec_closures::{corrected_invariant_names_and_locations, LoopSpecKind, SpecClosures}, translation::{fmir::{self, BorrowKind}, pearlite::Term}
};
use either::Either;
use rustc_borrowck::consumers::{
    BodyWithBorrowckFacts, BorrowIndex, BorrowSet, PlaceExt, RegionInferenceContext,
    TwoPhaseActivation,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::{Idx as _, bit_set::MixedBitSet};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    mir::{
        self, BasicBlock, Body, Local, Location, Place, PlaceRef, ProjectionElem, Rvalue,
        START_BLOCK, Statement, StatementKind, Terminator, TerminatorEdges, TerminatorKind,
        traversal::{self, reverse_postorder},
    },
    ty::{self, TyCtxt, TyKind, TypingEnv},
};
use rustc_mir_dataflow::{
    Analysis, ResultsCursor,
    impls::MaybeUninitializedPlaces,
    move_paths::{HasMoveData, LookupResult, MoveData, MovePathIndex},
    on_all_children_bits,
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_target::abi::{FieldIdx, VariantIdx};

use crate::extended_location::ExtendedLocation;

pub struct Resolver<'a, 'tcx> {
    live: ResultsCursor<'a, 'tcx, MaybeLiveExceptDrop<'a, 'tcx>>,
    uninit: ResultsCursor<'a, 'tcx, MaybeUninitializedPlaces<'a, 'tcx>>,
    borrows: ResultsCursor<'a, 'tcx, Borrows<'a, 'a, 'tcx>>,
    borrow_set: &'a BorrowSet<'tcx>,
    move_data: &'a MoveData<'tcx>,
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> HasMoveData<'tcx> for Resolver<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.move_data
    }
}

pub trait HasMoveDataExt<'tcx>: HasMoveData<'tcx> {
    fn empty_bitset(&self) -> MixedBitSet<MovePathIndex>;
}

impl<'tcx, T: HasMoveData<'tcx>> HasMoveDataExt<'tcx> for T {
    fn empty_bitset(&self) -> MixedBitSet<MovePathIndex> {
        MixedBitSet::new_empty(self.move_data().move_paths.len())
    }
}

#[derive(Debug)]
struct State {
    live: MixedBitSet<MovePathIndex>,
    uninit: MixedBitSet<MovePathIndex>,
    borrows: MixedBitSet<BorrowIndex>,
}

impl<'a, 'tcx> Resolver<'a, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        borrow_set: &'a BorrowSet<'tcx>,
        regioncx: &'a RegionInferenceContext<'tcx>,
        move_data: &'a MoveData<'tcx>,
    ) -> Resolver<'a, 'tcx> {
        let uninit = MaybeUninitializedPlaces::new(tcx, body, move_data)
            .mark_inactive_variants_as_uninit()
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);

        // MaybeLiveExceptDrop ignores `drop` for the purpose of resolve liveness... unclear that this can
        // be sound.
        let live = MaybeLiveExceptDrop::new(tcx, body, move_data)
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);

        let borrows = Borrows::new(tcx, body, &regioncx, borrow_set)
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);

        Resolver { live, uninit, borrows, borrow_set, move_data, body, tcx }
    }

    /// Get the set of frozen move paths corresponding to the given set of borrows.
    /// If both components of a tuple are borrowed, then each component is
    /// considered frozen independently, and not the parent move path.
    fn frozen_of_borrows(&self, borrows: &MixedBitSet<BorrowIndex>) -> MixedBitSet<MovePathIndex> {
        let mut frozen = self.empty_bitset();
        for bi in borrows.iter() {
            let place = self.borrow_set[bi].borrowed_place();
            match self.move_data().rev_lookup.find(place.as_ref()) {
                LookupResult::Exact(mp) => on_all_children_bits(&self.move_data(), mp, |mp| {
                    frozen.insert(mp);
                }),
                LookupResult::Parent(mp) => drop(frozen.insert(mp.unwrap())),
            };
        }
        frozen
    }

    /// Places that need to be resolved eventually
    /// = (live ∪ frozen) ∩ initialized
    fn need_resolve_places(&self, st: &State) -> MixedBitSet<MovePathIndex> {
        let mut should_resolve = self.frozen_of_borrows(&st.borrows);
        should_resolve.union(&st.live);
        should_resolve.subtract(&st.uninit);
        should_resolve
    }

    /// Places that have already been resolved
    /// = not live ∩ not frozen ∩ initialized
    /// = initialized - need_resolve_places
    fn resolved_places(&self, st: &State) -> MixedBitSet<MovePathIndex> {
        let mut x = self.frozen_of_borrows(&st.borrows);
        x.union(&st.live);
        x.union(&st.uninit);

        let mut resolved = self.empty_bitset();
        resolved.insert_all();
        resolved.subtract(&x);
        resolved
    }

    /// This function computes resolver state corresponding to the given extended location.
    /// It forwards the query to the underlying analyses, but treats specially two cases, by manually
    /// an partially applying parts of the transfer functions.
    ///    - If we ask for the mid state of a statement, then this statement is required to
    ///      be an assignment. In this case, we manually compute the state after RHS is evaluated
    ///      but before LHS is assigned (this more or less matches the mid state for a function call).
    ///    - If we ask to the end state of a terminator, then this statement is required to be a function
    ///      call. In this case, we manually compute the state after the assignement of the return place, but
    ///      before joining with other edges that would end up in the same block.
    fn state_at_loc(&mut self, loc: ExtendedLocation) -> State {
        let (mut uninit, mut live, mut borrows);
        match loc {
            ExtendedLocation::Mid(loc) if self.body.stmt_at(loc).is_left() => {
                // TODO: this is copying bits of the various analyses. Move this there,
                // and factor what can be factored.
                self.uninit.seek_before_primary_effect(loc);
                uninit = self.uninit.get().clone();
                for mi in &self.move_data().loc_map[loc] {
                    let path = mi.move_path_index(self.move_data());
                    on_all_children_bits(self.move_data(), path, |mpi| {
                        uninit.insert(mpi);
                    })
                }

                self.live.seek_before_primary_effect(loc);
                live = self.live.get().clone();
                let lhs_pl = match self.body.stmt_at(loc).left() {
                    Some(Statement { kind: StatementKind::Assign(box (pl, _)), .. }) => pl,
                    _ => unreachable!(),
                };
                match self.move_data().rev_lookup.find(lhs_pl.as_ref()) {
                    LookupResult::Exact(mp) => on_all_children_bits(self.move_data(), mp, |mpi| {
                        live.remove(mpi);
                    }),
                    LookupResult::Parent(Some(mp)) => {
                        if place_contains_borrow_deref(lhs_pl.as_ref(), self.body, self.tcx) {
                            live.insert(mp);
                        }
                    }
                    LookupResult::Parent(None) => unreachable!(),
                }

                self.borrows.seek_before_primary_effect(loc);
                borrows = self.borrows.get().clone();
                if let Some(indices) =
                    self.borrows.analysis().borrows_out_of_scope_at_location.get(&loc)
                {
                    for bi in indices {
                        borrows.remove(*bi);
                    }
                }
                if let Some(Statement {
                    kind: StatementKind::Assign(box (_, Rvalue::Ref(_, _, place))),
                    ..
                }) = self.body.stmt_at(loc).left()
                {
                    if !place.ignore_borrow(
                        self.tcx,
                        self.body,
                        &self.borrow_set.locals_state_at_exit(),
                    ) {
                        let index = BorrowIndex::from(
                            self.borrow_set.location_map().get_index_of(&loc).unwrap(),
                        );
                        borrows.insert(index);
                    }
                }
            }
            ExtendedLocation::End(loc) if let Either::Right(term) = self.body.stmt_at(loc) => {
                if let TerminatorEdges::AssignOnReturn { return_, place, .. } = term.edges() {
                    self.uninit.seek_after_primary_effect(loc);
                    uninit = self.uninit.get().clone();
                    self.uninit.mut_analysis().apply_call_return_effect(
                        &mut uninit,
                        loc.block,
                        place,
                    );

                    self.borrows.seek_before_primary_effect(loc);
                    borrows = self.borrows.get().clone();
                    self.borrows.mut_analysis().apply_call_return_effect(
                        &mut borrows,
                        loc.block,
                        place,
                    );

                    if return_.len() == 1 {
                        self.live.seek_after_primary_effect(return_[0].start_location());
                        live = self.live.get().clone();
                    } else {
                        assert_eq!(return_.len(), 0);
                        live = MixedBitSet::new_empty(self.move_data().move_paths.len());
                    }
                } else {
                    return self.state_at_loc(ExtendedLocation::Mid(loc));
                }
            }
            _ => {
                loc.seek_to(&mut self.uninit);
                uninit = self.uninit.get().clone();

                loc.seek_to(&mut self.live);
                live = self.live.get().clone();

                loc.seek_to(&mut self.borrows);
                borrows = self.borrows.get().clone();
            }
        }
        State { uninit, live, borrows }
    }

    pub fn need_resolve_resolved_places_at(
        &mut self,
        loc: ExtendedLocation,
    ) -> (MixedBitSet<MovePathIndex>, MixedBitSet<MovePathIndex>) {
        let st = self.state_at_loc(loc);
        (self.need_resolve_places(&st), self.resolved_places(&st))
    }

    pub fn resolved_places_during(
        &mut self,
        loc: ExtendedLocation,
    ) -> (MixedBitSet<MovePathIndex>, MixedBitSet<MovePathIndex>) {
        let (mut res, resolved) =
            self.need_resolve_resolved_places_at(ExtendedLocation::Start(loc.loc()));
        let st_after = self.state_at_loc(loc);

        // MixedBitSet::intersect is not implemented in rustc, substract is...
        //res.intersect(&self.resolved_places(&st_after));
        let mut not_res = res.clone();
        not_res.subtract(&self.resolved_places(&st_after));
        res.subtract(&not_res);

        (res, resolved)
    }

    pub fn resolved_places_between_blocks(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
    ) -> (MixedBitSet<MovePathIndex>, MixedBitSet<MovePathIndex>) {
        // if some places still need to be resolved at the end of the current block
        // but not at the start of the next block, we also need to resolve them now
        // see the init_join function in the resolve_uninit test

        let from_loc = ExtendedLocation::End(self.body.terminator_loc(from));
        let to_loc = ExtendedLocation::Start(to.start_location());

        let state_from = self.state_at_loc(from_loc);
        let state_to = self.state_at_loc(to_loc);

        let mut res = self.need_resolve_places(&state_from);
        res.subtract(&self.need_resolve_places(&state_to));

        (res, self.resolved_places(&state_from))
    }

    pub fn uninit_places_before(&mut self, loc: Location) -> MixedBitSet<MovePathIndex> {
        ExtendedLocation::Start(loc).seek_to(&mut self.uninit);
        self.uninit.get().clone()
    }

    pub fn live_places_before(&mut self, loc: Location) -> MixedBitSet<MovePathIndex> {
        ExtendedLocation::Start(loc).seek_to(&mut self.live);
        self.live.get().clone()
    }

    pub fn frozen_places_before(&mut self, loc: Location) -> MixedBitSet<MovePathIndex> {
        ExtendedLocation::Start(loc).seek_to(&mut self.borrows);
        self.frozen_of_borrows(self.borrows.get())
    }

    #[allow(dead_code)]
    pub(crate) fn debug(&mut self) {
        let body = self.body.clone();
        for (bb, bbd) in traversal::preorder(&body) {
            if bbd.is_cleanup {
                continue;
            }
            eprintln!("{:?}", bb);
            let mut loc = bb.start_location();
            for statement in &bbd.statements {
                let state1 = self.state_at_loc(ExtendedLocation::Start(loc));
                let live1 = state1.live.iter().collect::<Vec<_>>();
                let uninit1 = state1.uninit.iter().collect::<Vec<_>>();
                let frozen1 = self.frozen_of_borrows(&state1.borrows).iter().collect::<Vec<_>>();
                let need_resolve1 = self.need_resolve_places(&state1);

                let state2 = self.state_at_loc(ExtendedLocation::End(loc));
                let live2 = state2.live.iter().collect::<Vec<_>>();
                let uninit2 = state2.uninit.iter().collect::<Vec<_>>();
                let frozen2 = self.frozen_of_borrows(&state2.borrows).iter().collect::<Vec<_>>();
                let resolved2 = self.resolved_places(&state2);

                eprintln!("  {statement:?} {need_resolve1:?} -> {resolved2:?}");
                eprintln!(
                    "    live={live1:?} -> {live2:?} frozen={frozen1:?} -> {frozen2:?} uninit={uninit1:?} -> {uninit2:?}",
                );

                loc = loc.successor_within_block();
            }

            let state1 = self.state_at_loc(ExtendedLocation::Start(loc));
            let live1 = state1.live.iter().collect::<Vec<_>>();
            let uninit1 = state1.uninit.iter().collect::<Vec<_>>();
            let frozen1 = self.frozen_of_borrows(&state1.borrows).iter().collect::<Vec<_>>();
            let need_resolve1 = self.need_resolve_places(&state1);

            let state2 = self.state_at_loc(ExtendedLocation::End(loc));
            let live2 = state2.live.iter().collect::<Vec<_>>();
            let uninit2 = state2.uninit.iter().collect::<Vec<_>>();
            let frozen2 = self.frozen_of_borrows(&state2.borrows).iter().collect::<Vec<_>>();
            let resolved2 = self.resolved_places(&state2);

            eprintln!("  {:?} {need_resolve1:?} -> {resolved2:?}", bbd.terminator().kind);
            eprintln!(
                "    live={live1:?} -> {live2:?} frozen={frozen1:?} -> {frozen2:?} uninit={uninit1:?} -> {uninit2:?}",
            );
        }
        eprintln!();
    }
}

pub fn place_contains_borrow_deref<'tcx>(
    place: PlaceRef<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    place.iter_projections().any(|(pl, proj)| {
        proj == ProjectionElem::Deref
            && matches!(pl.ty(&body.local_decls, tcx).ty.kind(), TyKind::Ref(..))
    })
}

type Resolves<'tcx> = Vec<Place<'tcx>>;
type BorrowId = usize;

#[derive(TyEncodable, TyDecodable, Clone, Debug)]
pub struct BodyData<'tcx> {
    /// Resolves before each statement and terminator
    resolve_for_stmt: HashMap<Orphan<Location>, Resolves<'tcx>>,
    resolve_between_blocks: HashMap<BasicBlock, HashMap<BasicBlock, Resolves<'tcx>>>,
    final_borrows: HashMap<Orphan<Location>, BorrowId>,
    /// Locations where two-phase borrows are created.
    /// We will use this to delay the creation of two-phase borrows in our translation.
    two_phase_created: HashSet<Orphan<Location>>,
    /// Locations where two-phase borrows are activated, with the lhs, rhs of the borrow assignment, and whether the borrow is final
    two_phase_activated: HashMap<Orphan<Location>, Vec<(Place<'tcx>, Place<'tcx>, BorrowKind)>>,
}

// A newtype to carry orphan trait impls.
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

impl<'tcx> BodyData<'tcx> {
    pub fn new() -> Self {
        BodyData {
            resolve_for_stmt: HashMap::new(),
            resolve_between_blocks: HashMap::new(),
            two_phase_created: HashSet::new(),
            two_phase_activated: HashMap::new(),
            final_borrows: HashMap::new(),
        }
    }
}

pub struct Assertions<'tcx> {
    invariants: HashMap<BasicBlock, Vec<(LoopSpecKind, Term<'tcx>)>>,
    /// Invariants to translate as assertions.
    invariant_assertions: HashMap<DefId, (Term<'tcx>, String)>,
    /// Map of the `proof_assert!` blocks to their translated version.
    assertions: HashMap<DefId, Term<'tcx>>,
    /// Map of the `snapshot!` blocks to their translated version.
    snapshots: HashMap<DefId, Term<'tcx>>,
}

impl<'tcx> Assertions<'tcx> {
    fn empty() -> Self {
        Assertions {
            invariants: HashMap::new(),
            invariant_assertions: HashMap::new(),
            assertions: HashMap::new(),
            snapshots: HashMap::new(),
        }
    }
}

pub struct PreAnalysis<'a, 'tcx> {
    resolver: Resolver<'a, 'tcx>,
    erased_locals: MixedBitSet<Local>,
    typing_env: TypingEnv<'tcx>,
    /// Places to resolve before and after the current statement
    current_resolved: Vec<Place<'tcx>>,
    not_final_places: ResultsCursor<'a, 'tcx, NotFinalPlaces<'tcx>>,
    assertions: &'a Assertions<'tcx>,
    data: BodyData<'tcx>,
}

impl<'a, 'tcx> HasMoveData<'tcx> for PreAnalysis<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.resolver.move_data
    }
}

fn local_typing_env(tcx: TyCtxt<'_>, def_id: DefId) -> TypingEnv<'_> {
    let param_env = tcx.param_env(def_id);
    let typing_mode = ty::TypingMode::post_borrowck_analysis(tcx, def_id.as_local().unwrap());
    TypingEnv { typing_mode, param_env }
}

impl<'a, 'tcx> PreAnalysis<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a BodyWithBorrowckFacts<'tcx>,
        assertions: &'a Assertions<'tcx>,
        move_data: &'a MoveData<'tcx>,
    ) -> Self {
        let mut erased_locals = MixedBitSet::new_empty(body.body.local_decls.len());
        body.body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if is_spec(tcx, *def_id) || is_snapshot_closure(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });
        Self {
            resolver: Resolver::new(
                tcx,
                &body.body,
                &body.borrow_set,
                &body.region_inference_context,
                move_data,
            ),
            typing_env: local_typing_env(tcx, body.body.source.def_id()),
            erased_locals,
            current_resolved: Default::default(),
            not_final_places: NotFinalPlaces::new(tcx, &body.body)
                .iterate_to_fixpoint(tcx, &body.body, None)
                .into_results_cursor(&body.body),
            data: BodyData::new(),
            assertions,
        }
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
            if !self.erased_locals.contains(pl.local) {
                v.push(pl);
            }
        }

        for mp in to_resolve_partial.iter() {
            let pl = self.move_data().move_paths[mp].place;
            if self.erased_locals.contains(pl.local) {
                continue;
            }
            let ty = pl.ty(&self.body().local_decls, self.tcx());
            let ty = self.tcx().normalize_erasing_regions(self.typing_env, ty);
            let mut insert = |pl: Place<'tcx>| {
                if !matches!(self.move_data().rev_lookup.find(pl.as_ref()), LookupResult::Exact(_))
                {
                    v.push(pl)
                }
            };
            match ty.ty.kind() {
                TyKind::Adt(adt_def, subst) => {
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

                TyKind::Tuple(tys) => {
                    for (i, ty) in tys.iter().enumerate() {
                        insert(self.tcx().mk_place_field(pl, FieldIdx::new(i), ty));
                    }
                }

                TyKind::Closure(_did, substs) => {
                    for (i, ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                        insert(self.tcx().mk_place_field(pl, FieldIdx::new(i), ty));
                    }
                }

                TyKind::Array(_, _) | TyKind::Slice(_) | TyKind::Pat(_, _) => todo!(),

                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_)
                | TyKind::Foreign(_)
                | TyKind::Str
                | TyKind::RawPtr(_, _)
                | TyKind::Alias(_, _)
                | TyKind::Param(_)
                | TyKind::Bound(_, _)
                | TyKind::Placeholder(_)
                | TyKind::Infer(_)
                | TyKind::Error(_)
                | TyKind::Ref(_, _, _)
                | TyKind::FnDef(_, _)
                | TyKind::FnPtr(..)
                | TyKind::Dynamic(_, _, _)
                | TyKind::CoroutineClosure(_, _)
                | TyKind::Coroutine(_, _)
                | TyKind::CoroutineWitness(_, _)
                | TyKind::Never
                | TyKind::UnsafeBinder(_) => unreachable!("{}", ty.ty),
            }
        }

        // TODO determine resolution order based on outlives relation?
        v.sort_by_key(|pl| pl.local);
        for pl in v.into_iter().rev() {
            self.emit_resolve(pl);
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.resolver.tcx
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
            let TerminatorKind::SwitchInt { targets, .. } = &bbd.terminator().kind else {
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
                .resolve_between_blocks
                .entry(*pred)
                .or_insert(HashMap::new())
                .insert(bb, current_resolved);
        }

        // Find the place being discriminated, if there is one
        // TODO this is copy pasted, deduplicate
        fn discriminator_for_switch<'tcx>(bbd: &mir::BasicBlockData<'tcx>) -> Option<Place<'tcx>> {
            let discr = if let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind {
                discr
            } else {
                return None;
            };
            if let StatementKind::Assign(box (pl, Rvalue::Discriminant(real_discr))) =
                bbd.statements.last()?.kind
            {
                if discr.place() == Some(pl) { Some(real_discr) } else { None }
            } else {
                None
            }
        }
    }

    fn store_resolved_before(&mut self, loc: Location) {
        let resolved = std::mem::take(&mut self.current_resolved);
        self.data.resolve_for_stmt.insert(Orphan(loc), resolved);
    }

    fn visit(&mut self) {
        for (bb, bbd) in reverse_postorder(self.resolver.body) {
            if bbd.is_cleanup {
                continue;
            }
            self.resolve_places_between_blocks(bb);
            if bb == START_BLOCK {
                let (_, resolved) = self
                    .resolver
                    .need_resolve_resolved_places_at(ExtendedLocation::Start(Location::START));
                self.resolve_places(resolved.clone(), &resolved)
            }
            let mut loc = bb.start_location();
            for statement in &bbd.statements {
                self.visit_statement(statement, loc);
                loc = loc.successor_within_block();
            }
            self.visit_terminator(bbd.terminator(), loc);
            self.store_resolved_before(loc);
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, loc: Location) {
        self.activate_two_phase(loc);
        use StatementKind::*;
        match statement.kind {
            Assign(box (pl, ref rvalue)) => {
                let (need, resolved) =
                    self.resolver.resolved_places_during(ExtendedLocation::Mid(loc));
                self.resolve_before_assignment(need, &resolved, loc, pl);
                self.visit_assign(rvalue, loc);
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
                        if self.resolver.move_data.base_local(mp) == local {
                            need.insert(mp);
                        }
                    }
                }
                self.resolve_places(need, &resolved);
            }
            _ => {}
        }
    }

    fn visit_assign(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        match rvalue {
            Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, pl) => {
                if !self.is_two_phase(loc) {
                    self.check_final(pl, loc);
                }
            }
            _ => {}
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, loc: Location) {
        self.activate_two_phase(loc);
        match terminator.kind {
            TerminatorKind::Return => {
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
            TerminatorKind::Call { ref func, ref args, destination, target, fn_span, .. } => {
                let (need, resolved) =
                    self.resolver.resolved_places_during(ExtendedLocation::End(loc));
                self.resolve_before_assignment(need, &resolved, loc, destination);
                self.store_resolved_before(loc);
                if let Some(_) = target {
                    self.resolve_after_assignment(target.unwrap().start_location(), destination)
                }
            }
            TerminatorKind::Drop { target, place, .. } => {
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
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        &self.resolver.borrow_set
    }

    /// Store the location if it is a two-phase borrow creation.
    fn is_two_phase(&mut self, loc: Location) -> bool {
        let borrows = self.borrow_set();
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
        let borrows = &self.resolver.borrow_set;
        let mut activations = Vec::new();
        for i in borrows.activation_map().get(&loc).iter().flat_map(|is| is.iter()) {
            let borrow = &borrows[*i];
            let borrowed = borrow.borrowed_place();
            let is_final = NotFinalPlaces::is_final_at(not_final_places, &borrowed, loc);
            activations.push((borrow.assigned_place(), borrowed, is_final))
        }
        self.data.two_phase_activated.insert(Orphan(loc), activations);
    }

    fn check_final(&mut self, pl: &Place<'tcx>, loc: Location) {
        let is_final = NotFinalPlaces::is_final_at(self.not_final_places(), pl, loc);
        if let fmir::BorrowKind::Final(borrow_id) = is_final {
            self.insert_final_borrow(loc, borrow_id);
        }
    }

    fn not_final_places(&mut self) -> &mut ResultsCursor<'a, 'tcx, NotFinalPlaces<'tcx>> {
        &mut self.not_final_places
    }

    fn insert_final_borrow(&mut self, loc: Location, borrow_id: usize) {
        self.data.final_borrows.insert(Orphan(loc), borrow_id);
    }

    pub(crate) fn is_final(&self, loc: Location) -> fmir::BorrowKind {
        self.data
            .final_borrows
            .get(&Orphan(loc))
            .map_or(fmir::BorrowKind::Mut, |borrow_id| fmir::BorrowKind::Final(*borrow_id))
    }

    fn body(&self) -> &Body<'tcx> {
        self.resolver.body
    }
}

pub(crate) fn resolve_analysis(tcx: TyCtxt, def_id: LocalDefId) -> BodyData {
    let body = body_with_facts(tcx, def_id);
    resolve_analysis_for(tcx, &body, &Assertions::empty())
}

pub(crate) fn resolve_analysis_for<'tcx>(tcx: TyCtxt<'tcx>, body: &BodyWithBorrowckFacts<'tcx>, assertions: &Assertions<'tcx>) -> BodyData<'tcx> {
    let move_data = MoveData::gather_moves(&body.body, tcx, |_| true);
    let mut resolve_analysis = PreAnalysis::new(tcx, &body, assertions, &move_data);
    resolve_analysis.visit();
    resolve_analysis.data
}

fn get_assertions<'tcx>(ctx: &TranslationCtx<'tcx>, body: &Body<'tcx>) -> Assertions<'tcx> {
    let invariants = corrected_invariant_names_and_locations(ctx, body);
    let SpecClosures { assertions, snapshots } = SpecClosures::collect(ctx, body);
    Assertions {
        invariants: invariants.loop_headers,
        invariant_assertions: invariants.assertions,
        assertions,
        snapshots,
    }
}
