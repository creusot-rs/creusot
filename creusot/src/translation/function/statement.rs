use super::{BodyTranslator, TranslationError};
use crate::{
    analysis::NotFinalPlaces,
    contracts_items::{
        is_assertion, is_before_loop, is_invariant, is_snapshot_closure, is_spec, is_variant,
    },
    extended_location::ExtendedLocation,
    translation::{
        constant::from_ty_const,
        fmir::{self, Operand, RValue, inline_pearlite_subst},
    },
};
use rustc_borrowck::consumers::TwoPhaseActivation;
use rustc_middle::{
    mir::{
        BorrowKind::*, CastKind, Location, Operand::*, Place, Rvalue, SourceInfo, Statement,
        StatementKind,
    },
    ty::{TyKind, adjustment::PointerCoercion},
};
use rustc_mir_dataflow::ResultsCursor;
use rustc_span::Span;

impl<'tcx> BodyTranslator<'_, 'tcx> {
    pub(super) fn translate_statement(
        &mut self,
        not_final_borrows: &mut ResultsCursor<'_, 'tcx, NotFinalPlaces<'tcx>>,
        statement: &'_ Statement<'tcx>,
        loc: Location,
    ) -> Result<(), TranslationError> {
        let si = statement.source_info;
        self.activate_two_phase(not_final_borrows, loc, si.span);
        match statement.kind {
            StatementKind::Assign(box (pl, ref rv)) => {
                if let Some(resolver) = &mut self.resolver {
                    let (need, resolved) =
                        resolver.resolved_places_during(ExtendedLocation::Mid(loc));
                    self.resolve_before_assignment(need, &resolved, loc, pl)?;
                }

                self.translate_assign(not_final_borrows, si, &pl, rv, loc)?;

                if self.resolver.is_some() {
                    self.resolve_after_assignment(loc.successor_within_block(), pl)?;
                }
            }

            // All these instructions are no-ops in the dynamic semantics, but may trigger resolution
            StatementKind::Nop
            | StatementKind::StorageDead(_)
            | StatementKind::StorageLive(_)
            | StatementKind::FakeRead(_)
            | StatementKind::AscribeUserType(_, _)
            | StatementKind::Retag(_, _)
            | StatementKind::Coverage(_)
            | StatementKind::PlaceMention(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. } => {
                if let Some(resolver) = &mut self.resolver {
                    let (mut need, resolved) =
                        resolver.resolved_places_during(ExtendedLocation::End(loc));
                    if let StatementKind::StorageDead(local) | StatementKind::StorageLive(local) =
                        statement.kind
                    {
                        // These instructions signals that a local goes out of scope. We resolve any needed
                        // move path it contains. These are typically frozen places.
                        let (need_start, _) =
                            resolver.need_resolve_resolved_places_at(ExtendedLocation::Start(loc));
                        for mp in need_start.clone().iter() {
                            if self.move_data.base_local(mp) == local {
                                need.insert(mp);
                            }
                        }
                    }
                    self.resolve_places(need, &resolved)?;
                }
            }
            StatementKind::SetDiscriminant { .. } => self
                .ctx
                .crash_and_error(statement.source_info.span, "SetDiscriminant is not supported"),
            StatementKind::Intrinsic(_) => {
                self.ctx.crash_and_error(statement.source_info.span, "intrinsics are not supported")
            }
            StatementKind::Deinit(_) => unreachable!("Deinit unsupported"),
        }
        Ok(())
    }

    fn translate_assign(
        &mut self,
        not_final_borrows: &mut ResultsCursor<'_, 'tcx, NotFinalPlaces<'tcx>>,
        si: SourceInfo,
        place: &'_ Place<'tcx>,
        rvalue: &'_ Rvalue<'tcx>,
        loc: Location,
    ) -> Result<(), TranslationError> {
        let ty = rvalue.ty(self.body, self.tcx());
        let span = si.span;
        let rval: RValue<'tcx> = match rvalue {
            Rvalue::Use(op) => match op {
                Move(_pl) | Copy(_pl) => RValue::Operand(self.translate_operand(op)?),
                Constant(box c) => {
                    if let TyKind::Closure(def_id, _) = c.const_.ty().peel_refs().kind()
                        && is_snapshot_closure(self.tcx(), *def_id)
                    {
                        return Ok(());
                    };
                    RValue::Operand(self.translate_operand(op)?)
                }
            },
            Rvalue::Ref(_, ss, pl) => match ss {
                Shared | Fake(..) => {
                    if self.erased_locals.contains(pl.local) {
                        return Ok(());
                    }
                    RValue::Operand(Operand::Copy(self.translate_place(pl.as_ref())?))
                }
                Mut { .. } => {
                    if self.erased_locals.contains(pl.local) || self.is_two_phase(loc) {
                        return Ok(());
                    }
                    let is_final = NotFinalPlaces::is_final_at(
                        not_final_borrows,
                        pl,
                        loc.successor_within_block(),
                    );
                    self.emit_borrow(place, pl, is_final, span);
                    return Ok(());
                }
            },
            Rvalue::Discriminant(_) => return Ok(()),
            Rvalue::BinaryOp(op, box (l, r)) => {
                RValue::BinOp(*op, self.translate_operand(l)?, self.translate_operand(r)?)
            }
            Rvalue::UnaryOp(op, v) => RValue::UnaryOp(*op, self.translate_operand(v)?),
            Rvalue::Aggregate(box kind, ops) => {
                use rustc_middle::mir::AggregateKind::*;
                let fields =
                    ops.iter().map(|op| self.translate_operand(op)).collect::<Result<_, _>>()?;

                match kind {
                    Tuple => RValue::Tuple(fields),
                    Adt(adt, varix, subst, _, _) => {
                        let variant = self.ctx.adt_def(*adt).variant(*varix).def_id;
                        RValue::Constructor(variant, subst, fields)
                    }
                    Closure(def_id, subst) => {
                        if is_variant(self.tcx(), *def_id) || is_before_loop(self.tcx(), *def_id) {
                            return Ok(());
                        } else if is_invariant(self.tcx(), *def_id) {
                            match self.invariant_assertions.shift_remove(def_id) {
                                None => return Ok(()),
                                Some((mut cond, msg)) => {
                                    let places = self.tree.visible_places(si.scope);
                                    cond.subst(inline_pearlite_subst(self.ctx, &places));
                                    self.check_use_in_logic(&cond, loc);
                                    self.emit_statement(fmir::Statement::Assertion {
                                        cond,
                                        msg,
                                        trusted: false,
                                    });
                                    return Ok(());
                                }
                            }
                        } else if is_assertion(self.tcx(), *def_id) {
                            let mut assertion = self
                                .assertions
                                .shift_remove(def_id)
                                .expect("Could not find body of assertion");
                            let places = self.tree.visible_places(si.scope);
                            assertion.subst(inline_pearlite_subst(self.ctx, &places));
                            self.check_use_in_logic(&assertion, loc);
                            self.emit_statement(fmir::Statement::Assertion {
                                cond: assertion,
                                msg: "expl:assertion".to_owned(),
                                trusted: false,
                            });
                            return Ok(());
                        } else if is_spec(self.tcx(), *def_id) {
                            return Ok(());
                        } else {
                            RValue::Constructor(*def_id, subst, fields)
                        }
                    }
                    Array(_) => RValue::Array(fields),
                    _ => self.ctx.crash_and_error(
                        si.span,
                        &format!("the rvalue {:?} is not currently supported", kind),
                    ),
                }
            }
            Rvalue::Len(pl) => {
                let e = Operand::Copy(self.translate_place(pl.as_ref())?);
                RValue::Len(e)
            }
            Rvalue::Cast(CastKind::IntToInt | CastKind::PtrToPtr, op, cast_ty) => {
                let op_ty = op.ty(self.body, self.tcx());
                RValue::Cast(self.translate_operand(op)?, op_ty, *cast_ty)
            }
            Rvalue::Repeat(op, len) => RValue::Repeat(
                self.translate_operand(op)?,
                Operand::Constant(from_ty_const(
                    self.ctx,
                    *len,
                    self.ctx.types.usize,
                    self.typing_env(),
                    si.span,
                )),
            ),
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, _), op, ty) => {
                if let Some(t) = ty.builtin_deref(true)
                    && t.is_slice()
                {
                    // treat &[T; N] to &[T] casts as normal assignments
                    RValue::Operand(self.translate_operand(op)?)
                } else {
                    // TODO: Since we don't do anything with casts into `dyn` objects, just ignore them
                    return Ok(());
                }
            }
            Rvalue::RawPtr(_, pl) => RValue::Ptr(self.translate_place(pl.as_ref())?),
            Rvalue::Cast(
                CastKind::PointerCoercion(..)
                | CastKind::PointerExposeProvenance
                | CastKind::PointerWithExposedProvenance
                | CastKind::IntToFloat
                | CastKind::FloatToInt
                | CastKind::FnPtrToPtr
                | CastKind::FloatToFloat
                | CastKind::Transmute,
                _,
                _,
            ) => self.ctx.crash_and_error(
                si.span,
                &format!("Pointer casts are currently unsupported {rvalue:?}"),
            ),
            Rvalue::CopyForDeref(_)
            | Rvalue::ShallowInitBox(_, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::ThreadLocalRef(_) => self.ctx.crash_and_error(
                si.span,
                &format!("MIR code used an unsupported Rvalue {:?}", rvalue),
            ),
        };

        if !ty.is_unit() {
            self.emit_assignment(place, rval, span);
        }
        Ok(())
    }

    fn is_two_phase(&self, loc: Location) -> bool {
        let Some(borrows) = &self.borrows else { return false };
        borrows.location_map().get(&loc).iter().any(|borrow| {
            matches!(borrow.activation_location(), TwoPhaseActivation::ActivatedAt(_))
        })
    }

    pub(super) fn activate_two_phase(
        &mut self,
        not_final_borrows: &mut ResultsCursor<'_, 'tcx, NotFinalPlaces<'tcx>>,
        loc: Location,
        span: Span,
    ) {
        let Some(borrows) = self.borrows else { return };
        for i in borrows.activation_map().get(&loc).iter().flat_map(|is| is.iter()) {
            let borrow = &borrows[*i];
            let borrowed = borrow.borrowed_place();
            let is_final = NotFinalPlaces::is_final_at(not_final_borrows, &borrowed, loc);
            self.emit_borrow(&borrow.assigned_place(), &borrowed, is_final, span)
        }
    }
}
