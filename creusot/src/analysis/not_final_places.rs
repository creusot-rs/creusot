use rustc_borrowck::consumers::PlaceConflictBias;
use rustc_index::bit_set::MixedBitSet;
use rustc_middle::{
    mir::{
        self, Location, Place, PlaceRef, ProjectionElem, TerminatorKind,
        visit::{MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor},
    },
    ty::{List, TyCtxt},
};
use rustc_mir_dataflow::{Analysis, Backward, GenKill, ResultsCursor, fmt::DebugWithContext};
use std::{
    collections::{HashMap, hash_map},
    iter::once,
};

use crate::{extended_location::ExtendedLocation, translation::fmir::BorrowKind};

type PlaceId = usize;

#[derive(Clone, Debug, Default)]
struct PlaceInfo<'tcx> {
    /// ID of this place.
    ///
    /// This is necessary to use a `ChunkedBitSet<PlaceId>`.
    id: PlaceId,
    /// The number of mutable derefs this place contains.
    deref_count: usize,
    /// The set of subplaces of this place.
    ///
    /// A `p1` is a subplace of `p2` if they refer to the same local variable, and
    /// `p2.projection` is a prefix of `p1.projection`.
    subplaces: Vec<PlaceRef<'tcx>>,
    /// The set of places that conflict with this place, but are NOT a subplace.
    ///
    /// Two places `p1` and `p2` are conflicting if they may refer to the same memory location
    conflicting: Vec<PlaceRef<'tcx>>,
}

pub struct NotFinalPlaces<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Maps an ID to its place
    places: Vec<PlaceRef<'tcx>>,
    /// Places organized by their local.
    places_per_local: HashMap<mir::Local, Vec<PlaceRef<'tcx>>>,
    infos: HashMap<PlaceRef<'tcx>, PlaceInfo<'tcx>>,
}

fn place_has_deref_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: PlaceRef<'tcx>,
) -> bool {
    for (p, elem) in place.iter_projections() {
        if matches!(elem, ProjectionElem::Deref) {
            let ty_kind = p.ty(body, tcx).ty.kind();
            match ty_kind {
                rustc_type_ir::TyKind::Ref(_, _, mutability) => {
                    if !mutability.is_mut() {
                        return true;
                    }
                }
                _ => {}
            }
        }
    }
    false
}

impl<'tcx> NotFinalPlaces<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Self {
        #[derive(Default)]
        struct VisitAllPlaces<'tcx> {
            places: Vec<PlaceRef<'tcx>>,
            places_ids: HashMap<PlaceRef<'tcx>, PlaceId>,
            places_per_local: HashMap<mir::Local, Vec<PlaceRef<'tcx>>>,
        }
        impl<'tcx> Visitor<'tcx> for VisitAllPlaces<'tcx> {
            fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
                let place_ref = place.as_ref();
                for place in once(place_ref).chain(place_ref.iter_projections().map(|(p, _)| p)) {
                    let idx = self.places_ids.len();
                    if let hash_map::Entry::Vacant(entry) = self.places_ids.entry(place) {
                        self.places.push(place);
                        self.places_per_local.entry(place.local).or_default().push(place);
                        entry.insert(idx);
                    }
                }
            }
        }

        let mut visitor = VisitAllPlaces::default();
        visitor.visit_body(body);
        let places = visitor.places;
        let places_ids = visitor.places_ids;
        let places_per_local = {
            let mut per_local = visitor.places_per_local;
            for places in per_local.values_mut() {
                places.sort_by_key(|p| p.projection.len());
            }
            per_local
        };
        let mut infos = HashMap::new();

        // pre-processing: determine subplaces, conflicting places, places with deref
        for places in places_per_local.values() {
            for &place in places {
                let entry: &mut PlaceInfo = infos.entry(place).or_default();
                entry.id = places_ids[&place];
                entry.deref_count = Self::place_count_derefs(place, body, tcx);
                for &other_place in places {
                    if place == other_place {
                        continue;
                    }
                    let mut subplace = false;
                    if other_place.projection.get(..place.projection.len())
                        == Some(place.projection)
                    {
                        subplace = true;
                        entry.subplaces.push(other_place);
                    }

                    // We use `PlaceConflictBias::Overlap`, because we assume that unknown index accesses _do_ overlap.

                    // This function would crash if `place` is a `*x` where `x: &T`.
                    // But we filtered such places in the visitor.
                    if !subplace
                        // This is required for `rustc_borrowck::consumers::places_conflict` to not crash.
                        && !place_has_deref_ref(tcx, body, place)
                        && !place_has_deref_ref(tcx, body, other_place)
                        && rustc_borrowck::consumers::places_conflict(
                            tcx,
                            body,
                            place.to_place(tcx),
                            other_place.to_place(tcx),
                            PlaceConflictBias::Overlap,
                        )
                    {
                        entry.conflicting.push(other_place);
                    }
                }
            }
        }
        Self { tcx, places, places_per_local, infos }
    }

    /// Run the analysis right **after** `location`, and determines if the borrow of
    /// `place` is a final reborrow.
    ///
    /// # Returns
    /// - If the reborrow is final, return `Final` with the position of the dereference of the
    /// original borrow in `place.projection`.
    ///
    ///   For example, if the reborrow `&mut (*x.0)` is final, then the projections are
    /// `[Field(0), Deref]`, and so we return `Final(1)`.
    ///
    ///   `Deref` of a box is not considered as a dereference of a borrow.
    /// - Else, return `Mut`.
    pub fn is_final_at(
        cursor: &mut ResultsCursor<'_, 'tcx, Self>,
        place: &Place<'tcx>,
        location: Location,
    ) -> BorrowKind {
        let body = cursor.body();
        let tcx = cursor.analysis().tcx;

        let deref_position = match Self::place_get_last_deref(place.as_ref(), body, tcx) {
            Some(p) => p,
            // `p` is not a reborrow
            None => return BorrowKind::Mut,
        };

        ExtendedLocation::Start(location).seek_to(cursor);
        let analysis: &Self = cursor.analysis();

        let id = analysis.infos[&place.as_ref()].id;
        if cursor.get().contains(id) {
            return BorrowKind::Mut;
        }
        BorrowKind::Final(deref_position)
    }

    /// Helper function: gets the index of the last projection of `place` that is a deref,
    /// but not a deref of a box.
    fn place_get_last_deref(
        place: PlaceRef<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<usize> {
        let pos_from_end = place.iter_projections().rev().position(|(pl, proj)| {
            proj == ProjectionElem::Deref && !pl.ty(&body.local_decls, tcx).ty.is_box()
        })?;
        Some(place.projection.len() - pos_from_end - 1)
    }

    /// Helper function: gets the index of the first projection of `place` that is a deref,
    /// but not a deref of a box.
    fn place_count_derefs(
        place: PlaceRef<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> usize {
        let mut result = 0;
        for (pl, proj) in place.iter_projections() {
            if proj == ProjectionElem::Deref && !pl.ty(&body.local_decls, tcx).ty.is_box() {
                result += 1;
            }
        }
        result
    }
}

impl<'tcx> DebugWithContext<NotFinalPlaces<'tcx>> for MixedBitSet<PlaceId> {
    fn fmt_with(
        &self,
        ctxt: &NotFinalPlaces<'tcx>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        f.debug_list().entries(self.iter().map(|id| ctxt.places[id])).finish()
    }
}

// The NotFinalPlaces analysis computes, for each location, places which either:
// - do not contain a mutable borrow deref and may be moved or borrowed in the future
//      i.e., if such a place contains a borrow, then this borrow may be written to before its resolution
// - do contain one or more mutable borrow deref, and may be written to in the future

impl<'tcx> Analysis<'tcx> for NotFinalPlaces<'tcx> {
    type Domain = MixedBitSet<PlaceId>;
    type Direction = Backward;

    const NAME: &'static str = "not_final_places";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = all borrows are final
        MixedBitSet::new_empty(self.places.len())
    }

    // no initialization, because we are doing backward analysis.
    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {}

    fn apply_primary_statement_effect(
        &mut self,
        trans: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        PlaceVisitor { info: self, trans }.visit_statement(statement, location);
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> mir::TerminatorEdges<'mir, 'tcx> {
        let mut visitor = PlaceVisitor { info: self, trans };
        if terminator.kind == TerminatorKind::Return {
            for &p in &self.places {
                visitor.write_local(p.local);
            }
        }
        visitor.visit_terminator(terminator, location);
        terminator.edges()
    }
}

struct PlaceVisitor<'a, 'tcx, T> {
    info: &'a NotFinalPlaces<'tcx>,
    trans: &'a mut T,
}

impl<'tcx, T> PlaceVisitor<'_, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    /// A write into `p`, changing its prophecy.
    ///
    /// This place and all its subplaces/conflicting places will be marked non-final,
    /// _but_ subplaces that have exactly one more dereference than `p` will become final.
    fn write(&mut self, p: PlaceRef<'tcx>) {
        let infos = &self.info.infos[&p];
        self.trans.gen_(infos.id);
        for subplace in &infos.subplaces {
            let sub_infos = &self.info.infos[subplace];
            if sub_infos.deref_count == infos.deref_count + 1 {
                self.trans.kill(sub_infos.id);
            } else {
                self.trans.gen_(sub_infos.id);
            }
        }
        for conflict in &infos.conflicting {
            let sub_infos = &self.info.infos[conflict];
            self.trans.gen_(sub_infos.id);
        }
    }

    /// All the places with local `l` and 1 deref will be marked final.
    ///
    /// Other places with local `l` will be marked non-final.
    fn write_local(&mut self, l: mir::Local) {
        let Some(places) = self.info.places_per_local.get(&l) else {
            return;
        };
        for p in places {
            let infos = &self.info.infos[p];
            if infos.deref_count == 1 {
                self.trans.kill(infos.id);
            } else {
                self.trans.gen_(infos.id);
            }
        }
    }

    /// We are moving from `p`, preventing us from statically knowing the modification to
    /// its prophecy. Note that this is also true if `p` is being borrrowed.
    ///
    /// All subplaces of `p` will be marked non-final, as well as places conflicting with `p`.
    fn move_(&mut self, p: PlaceRef<'tcx>) {
        let infos = &self.info.infos[&p];
        self.trans.gen_(infos.id);
        for p2 in infos.conflicting.iter().chain(&infos.subplaces) {
            self.trans.gen_(self.info.infos[p2].id);
        }
    }
}

impl<'tcx, T> Visitor<'tcx> for PlaceVisitor<'_, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _: Location) {
        match context {
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                self.move_(place.as_ref());
            }
            PlaceContext::MutatingUse(context) => match context {
                MutatingUseContext::Store
                | MutatingUseContext::SetDiscriminant
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Call
                | MutatingUseContext::Drop => self.write(place.as_ref()),
                MutatingUseContext::Borrow => {
                    self.move_(place.as_ref());
                }
                _ => {}
            },
            PlaceContext::NonUse(NonUseContext::StorageLive | NonUseContext::StorageDead) => {
                self.write(place.as_ref())
            }
            _ => {}
        }
    }

    fn visit_local(&mut self, local: mir::Local, context: PlaceContext, _: Location) {
        match context {
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                self.move_(Place { local, projection: List::empty() }.as_ref());
            }
            PlaceContext::MutatingUse(context) => match context {
                MutatingUseContext::Store
                | MutatingUseContext::Drop
                | MutatingUseContext::SetDiscriminant
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Call => self.write_local(local),
                MutatingUseContext::Borrow => {
                    self.move_(Place { local, projection: List::empty() }.as_ref());
                }
                _ => {}
            },
            PlaceContext::NonUse(NonUseContext::StorageLive | NonUseContext::StorageDead) => {
                self.write_local(local)
            }
            _ => {}
        }
    }
}
