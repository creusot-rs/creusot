use rustc_middle::{
    mir::{
        Body, HasLocalDecls, Location, Place, PlaceElem, PlaceTy,
        visit::{NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::TyKind,
};

use crate::{
    backend::projections::projection_ty,
    contracts_items::Intrinsic,
    ctx::{HasTyCtxt, TranslationCtx},
};

pub struct GuardedMoveVisitor<'tcx, 'a> {
    pub ctx: &'a TranslationCtx<'tcx>,
    pub body: &'a Body<'tcx>,
}

impl<'tcx, 'a> Visitor<'tcx> for GuardedMoveVisitor<'tcx, 'a> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.super_place(place, context, location);
        let PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) = context else { return };
        let mut ty = PlaceTy::from_ty(self.body.local_decls()[place.local].ty);
        for p in place.projection.iter() {
            if let PlaceElem::Field(_, _) = p
                && let TyKind::Adt(def, _) = ty.ty.kind()
                && Intrinsic::Guarded.is(self.ctx, def.did())
            {
                self.ctx
                    .error(
                        self.body.source_info(location).span,
                        "Cannot move out of a Guarded value",
                    )
                    .emit();
            }

            ty = projection_ty(ty, self.ctx.tcx, &p);
        }
    }
}
