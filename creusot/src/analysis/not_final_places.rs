use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::Mutability;
use rustc_index::{IndexVec, bit_set::MixedBitSet};
use rustc_middle::{
    mir::{
        Body, Local, Location, Place, PlaceRef, PlaceTy, ProjectionElem, Statement, Terminator,
        TerminatorEdges, TerminatorKind,
        visit::{MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{Analysis, Backward, GenKill, ResultsCursor, fmt::DebugWithContext};
use std::{
    collections::{HashMap, hash_map},
    iter::once,
};

use crate::{
    backend::projections::projection_ty, extended_location::ExtendedLocation,
    translation::fmir::BorrowKind,
};

rustc_index::newtype_index! {
    pub struct PlaceId {}
}

#[derive(Clone, Debug)]
struct PlaceInfo<'tcx> {
    place: PlaceRef<'tcx>,
    /// The number of mutable derefs this place contains.
    deref_count: usize,
    /// The set of subplaces of this place.
    ///
    /// Place `p1` is a subplace of `p2` if they refer to the same local variable, and
    /// `p2.projection` is a strict prefix of `p1.projection`.
    subplaces: MixedBitSet<PlaceId>,
    /// The set of places that conflict with this place, but are NOT a subplace.
    ///
    /// Two places `p1` and `p2` are conflicting if they may refer to the same memory location
    conflicting: MixedBitSet<PlaceId>,
}

/// A notion of projection that do not contain types nor indices, so that quality/hash mean what
/// we expect.
#[derive(Hash, PartialEq, Eq, Clone, Copy)]
enum HProjectionElem {
    DerefBox,
    DerefShrBor,
    DerefMutBor,
    Field(FieldIdx),
    Downcast(VariantIdx),
    Index,
}

impl HProjectionElem {
    fn from_projection_elem<'tcx>(
        p: ProjectionElem<Local, Ty<'tcx>>,
        place_ty: PlaceTy<'tcx>,
    ) -> Option<Self> {
        match p {
            ProjectionElem::Deref => match place_ty.ty.kind() {
                TyKind::Ref(_, _, Mutability::Mut) => Some(Self::DerefMutBor),
                TyKind::Ref(_, _, Mutability::Not) => Some(Self::DerefShrBor),
                TyKind::Adt(def, _) if def.is_box() => Some(Self::DerefBox),
                _ => None,
            },
            ProjectionElem::Field(field_idx, _) => Some(Self::Field(field_idx)),
            ProjectionElem::Downcast(_, variant_idx) => Some(Self::Downcast(variant_idx)),
            ProjectionElem::Index(_) => Some(Self::Index),
            ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::UnwrapUnsafeBinder(_) => None,
        }
    }
}

#[derive(Hash, PartialEq, Eq, Clone)]
struct HPlace {
    local: Local,
    projection: Vec<HProjectionElem>,
}

impl HPlace {
    fn from_place<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, p: PlaceRef<'tcx>) -> (Self, bool) {
        let mut place_ty = PlaceTy::from_ty(body.local_decls[p.local].ty);
        let projection: Vec<HProjectionElem> = p
            .projection
            .iter()
            .map_while(|proj| {
                let r = HProjectionElem::from_projection_elem(*proj, place_ty)?;
                place_ty = projection_ty(place_ty, tcx, &proj);
                Some(r)
            })
            .collect();
        let full = projection.len() == p.projection.len();
        (HPlace { local: p.local, projection }, full)
    }

    fn ambiguous(&self) -> bool {
        self.projection.iter().any(|&p| p == HProjectionElem::Index)
    }
}

pub struct NotFinalPlaces<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    /// Maps a place to its ID
    places_ids: HashMap<HPlace, PlaceId>,
    /// Places organized by their local.
    places_per_local: HashMap<Local, MixedBitSet<PlaceId>>,
    infos: IndexVec<PlaceId, PlaceInfo<'tcx>>,
}

impl<'a, 'tcx> NotFinalPlaces<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        struct VisitAllPlaces<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            body: &'a Body<'tcx>,
            places: IndexVec<PlaceId, (PlaceRef<'tcx>, HPlace)>,
            places_ids: HashMap<HPlace, PlaceId>,
            places_per_local: HashMap<Local, Vec<PlaceId>>,
        }
        impl<'a, 'tcx> Visitor<'tcx> for VisitAllPlaces<'a, 'tcx> {
            fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
                let place_ref = place.as_ref();
                for place in once(place_ref).chain(place_ref.iter_projections().map(|(p, _)| p)) {
                    let (hplace, full) = HPlace::from_place(self.tcx, self.body, place);
                    if !full {
                        break;
                    }
                    if let hash_map::Entry::Vacant(entry) = self.places_ids.entry(hplace.clone()) {
                        let id = self.places.push((place, hplace));
                        self.places_per_local.entry(place.local).or_default().push(id);
                        entry.insert(id);
                    }
                }
            }
        }

        let mut visitor = VisitAllPlaces {
            tcx,
            body,
            places: Default::default(),
            places_ids: Default::default(),
            places_per_local: Default::default(),
        };
        visitor.visit_body(body);
        let VisitAllPlaces { places, places_ids, places_per_local: ppl, .. } = visitor;

        let empty_bs = MixedBitSet::new_empty(places.len());
        let places_per_local: HashMap<Local, MixedBitSet<PlaceId>> = ppl
            .into_iter()
            .map(|(l, places)| {
                let mut r = empty_bs.clone();
                for id in places {
                    r.insert(id);
                }
                (l, r)
            })
            .collect();

        // pre-processing: determine subplaces, conflicting places, places with deref
        let infos = places
            .iter_enumerated()
            .map(|(place_id, &(place, ref hplace))| {
                let (mut conflicting, mut subplaces) = (empty_bs.clone(), empty_bs.clone());
                for other_id in
                    places_per_local[&place.local].iter().filter(|&other_id| other_id != place_id)
                {
                    let (_, other_hplace) = &places[other_id];
                    if other_hplace.projection.get(..hplace.projection.len())
                        == Some(&*hplace.projection)
                    {
                        subplaces.insert(other_id);
                    } else if hplace.projection.get(..other_hplace.projection.len())
                        == Some(&other_hplace.projection)
                    {
                        conflicting.insert(other_id);
                    }
                }

                let deref_count = hplace
                    .projection
                    .iter()
                    .filter(|&&p| p == HProjectionElem::DerefMutBor)
                    .count();
                PlaceInfo { place, deref_count, subplaces, conflicting }
            })
            .collect();

        Self { tcx, body, places_per_local, infos, places_ids }
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
        let (hplace, true) = HPlace::from_place(tcx, body, place.as_ref()) else {
            // This place is too complex for this analysis
            return BorrowKind::Mut;
        };
        let Some(deref_pos_from_end) =
            hplace.projection.iter().rev().position(|e| matches!(e, HProjectionElem::DerefMutBor))
        else {
            // `p` is not a reborrow
            return BorrowKind::Mut;
        };

        ExtendedLocation::Start(location).seek_to(cursor);
        let id = cursor.analysis().places_ids[&hplace];
        if cursor.get().contains(id) {
            return BorrowKind::Mut;
        } else {
            return BorrowKind::Final(hplace.projection.len() - deref_pos_from_end - 1);
        }
    }
}

impl<'a, 'tcx> DebugWithContext<NotFinalPlaces<'a, 'tcx>> for MixedBitSet<PlaceId> {
    fn fmt_with(
        &self,
        ctxt: &NotFinalPlaces<'a, 'tcx>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        f.debug_list().entries(self.iter().map(|id| ctxt.infos[id].place)).finish()
    }
}

// The NotFinalPlaces analysis computes, for each location, places which either:
// - do not contain a mutable borrow deref and may be moved or borrowed in the future
//      i.e., if such a place contains a borrow, then this borrow may be written to before its resolution
// - do contain one or more mutable borrow deref, and may be written to in the future

impl<'a, 'tcx> Analysis<'tcx> for NotFinalPlaces<'a, 'tcx> {
    type Domain = MixedBitSet<PlaceId>;
    type Direction = Backward;

    const NAME: &'static str = "not_final_places";

    fn bottom_value(&self, _: &Body<'tcx>) -> Self::Domain {
        // bottom = all borrows are final
        MixedBitSet::new_empty(self.infos.len())
    }

    // no initialization, because we are doing backward analysis.
    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {}

    fn apply_primary_statement_effect(
        &self,
        trans: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        PlaceVisitor { info: self, trans }.visit_statement(statement, location);
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        trans: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let mut visitor = PlaceVisitor { info: self, trans };
        if terminator.kind == TerminatorKind::Return {
            for &l in self.places_per_local.keys() {
                visitor.write_local(l);
            }
        }
        visitor.visit_terminator(terminator, location);
        terminator.edges()
    }
}

struct PlaceVisitor<'a, 'tcx, T> {
    info: &'a NotFinalPlaces<'a, 'tcx>,
    trans: &'a mut T,
}

impl<'tcx, T> PlaceVisitor<'_, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    /// A write into `p`, changing its current value.
    ///
    /// This place and all its subplaces/conflicting places will be marked non-final,
    /// _but_ subplaces that have exactly one more dereference than `p` will become final.
    fn write(&mut self, p: &Place<'tcx>) {
        let (hplace, full) = HPlace::from_place(self.info.tcx, self.info.body, p.as_ref());
        let id = self.info.places_ids[&hplace];
        let infos = &self.info.infos[id];
        self.trans.gen_(id);
        self.trans.gen_all(infos.conflicting.iter());
        for subplace_id in infos.subplaces.iter() {
            if self.info.infos[subplace_id].deref_count == infos.deref_count + 1 {
                if full && !hplace.ambiguous() {
                    self.trans.kill(subplace_id);
                }
            } else {
                self.trans.gen_(subplace_id);
            }
        }
    }

    /// All the places with local `l` and 1 deref will be marked final.
    ///
    /// Other places with local `l` will be marked non-final.
    fn write_local(&mut self, l: Local) {
        let Some(places) = self.info.places_per_local.get(&l) else {
            return;
        };
        for id in places.iter() {
            if self.info.infos[id].deref_count == 1 {
                self.trans.kill(id);
            } else {
                self.trans.gen_(id);
            }
        }
    }

    /// We are moving from `p`, preventing us from statically knowing the modification to
    /// its current value. Note that this is also true if `p` is being borrrowed.
    ///
    /// All subplaces of `p` will be marked non-final, as well as places conflicting with `p`.
    fn move_or_bor(&mut self, p: &Place<'tcx>) {
        let (hplace, _) = HPlace::from_place(self.info.tcx, self.info.body, p.as_ref());
        let id = self.info.places_ids[&hplace];
        let infos = &self.info.infos[id];
        self.trans.gen_(id);
        self.trans.gen_all(infos.conflicting.iter());
        self.trans.gen_all(infos.subplaces.iter())
    }
}

impl<'tcx, T> Visitor<'tcx> for PlaceVisitor<'_, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _: Location) {
        match context {
            PlaceContext::MutatingUse(
                MutatingUseContext::Store
                | MutatingUseContext::SetDiscriminant
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Call
                | MutatingUseContext::Drop,
            ) => self.write(place),
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
            | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => self.move_or_bor(place),
            _ => {}
        }
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        match context {
            PlaceContext::NonUse(NonUseContext::StorageLive | NonUseContext::StorageDead) => {
                self.write_local(local)
            }
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
            | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
                self.move_or_bor(&local.into())
            }
            _ => {}
        }
    }
}
