use super::BodyTranslator;
use crate::{
    analysis::NotFinalPlaces,
    attributes::{is_assertion, is_invariant, is_spec, is_variant, snapshot_closure_id},
    extended_location::ExtendedLocation,
    fmir::Operand,
    translation::{
        fmir::{self, RValue},
        specification::inv_subst,
    },
};
use rustc_borrowck::borrow_set::TwoPhaseActivation;
use rustc_middle::{
    mir::{
        BinOp, BorrowKind::*, CastKind, Location, Operand::*, Place, Rvalue, SourceInfo, Statement,
        StatementKind,
    },
    ty::adjustment::PointerCoercion,
};
use rustc_mir_dataflow::ResultsCursor;

impl<'tcx> BodyTranslator<'_, 'tcx> {
    pub fn translate_statement(
        &mut self,
        not_final_borrows: &mut ResultsCursor<'_, 'tcx, NotFinalPlaces<'tcx>>,
        statement: &'_ Statement<'tcx>,
        loc: Location,
    ) {
        use StatementKind::*;
        match statement.kind {
            Assign(box (pl, ref rv)) => {
                if let Some(resolver) = &mut self.resolver {
                    let (need, resolved) =
                        resolver.resolved_places_during(ExtendedLocation::Mid(loc));
                    self.resolve_before_assignment(need, &resolved, loc, pl);
                }

                self.translate_assign(not_final_borrows, statement.source_info, &pl, rv, loc);

                if self.resolver.is_some() {
                    self.resolve_after_assignment(loc.successor_within_block(), pl)
                }
            }

            // All these instructions are no-opsin the dynamic semantics, but may trigger resolution
            Nop
            | StorageDead(_)
            | StorageLive(_)
            | FakeRead(_)
            | AscribeUserType(_, _)
            | Retag(_, _)
            | Coverage(_)
            | PlaceMention(_)
            | ConstEvalCounter => {
                if let Some(resolver) = &mut self.resolver {
                    let (mut need, resolved) =
                        resolver.resolved_places_during(ExtendedLocation::End(loc));
                    if let StorageDead(local) | StorageLive(local) = statement.kind {
                        // These instructions signals that a local goes out of scope. We resolve any needed
                        // move path it contains. These are typically frozen places.
                        let (need_start, _) =
                            resolver.need_resolve_resolved_places_at(ExtendedLocation::Start(loc));
                        for mp in need_start.clone().iter() {
                            if self.mdpe.move_data.base_local(mp) == local {
                                need.insert(mp);
                            }
                        }
                    }
                    self.resolve_places(need, &resolved);
                }
            }
            SetDiscriminant { .. } => self
                .ctx
                .crash_and_error(statement.source_info.span, "SetDiscriminant is not supported"),
            Intrinsic(_) => {
                self.ctx.crash_and_error(statement.source_info.span, "intrinsics are not supported")
            }
            Deinit(_) => unreachable!("Deinit unsupported"),
        }
    }

    fn translate_assign(
        &mut self,
        not_final_borrows: &mut ResultsCursor<'_, 'tcx, NotFinalPlaces<'tcx>>,
        si: SourceInfo,
        place: &'_ Place<'tcx>,
        rvalue: &'_ Rvalue<'tcx>,
        loc: Location,
    ) {
        let ty = rvalue.ty(self.body, self.tcx());
        let span = si.span;
        let rval: RValue<'tcx> = match rvalue {
            Rvalue::Use(op) => match op {
                Move(_pl) | Copy(_pl) => RValue::Operand(self.translate_operand(op)),
                Constant(box c) => {
                    if snapshot_closure_id(self.tcx(), c.const_.ty()).is_some() {
                        return;
                    };
                    RValue::Operand(self.translate_operand(op))
                }
            },
            Rvalue::Ref(_, ss, pl) => match ss {
                Shared | Fake(..) => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }

                    let op = Operand::Copy(
                        self.translate_place(self.compute_ref_place(*pl, loc).as_ref()),
                    );
                    RValue::Operand(op)
                }
                Mut { .. } => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }

                    let is_final = NotFinalPlaces::is_final_at(not_final_borrows, pl, loc);
                    self.emit_borrow(place, pl, is_final, span);
                    return;
                }
            },
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(BinOp::BitAnd, box (l, _))
                if !l.ty(self.body, self.tcx()).is_bool() =>
            {
                self.ctx.crash_and_error(si.span, "bitwise operations are currently unsupported")
            }
            Rvalue::BinaryOp(op, box (l, r)) => {
                RValue::BinOp(*op, self.translate_operand(l), self.translate_operand(r))
            }
            Rvalue::UnaryOp(op, v) => RValue::UnaryOp(*op, self.translate_operand(v)),
            Rvalue::Aggregate(box kind, ops) => {
                use rustc_middle::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op)).collect();

                match kind {
                    Tuple => RValue::Tuple(fields),
                    Adt(adt, varix, subst, _, _) => {
                        let variant = self.ctx.adt_def(*adt).variant(*varix).def_id;
                        RValue::Constructor(variant, subst, fields)
                    }
                    Closure(def_id, subst) => {
                        if is_invariant(self.tcx(), *def_id) || is_variant(self.tcx(), *def_id) {
                            return;
                        } else if is_assertion(self.tcx(), *def_id) {
                            let mut assertion = self
                                .assertions
                                .remove(def_id)
                                .expect("Could not find body of assertion");
                            assertion.subst(&inv_subst(self.tcx(), &self.body, &self.locals, si));
                            self.check_frozen_in_logic(&assertion, loc);
                            self.emit_statement(fmir::Statement::Assertion {
                                cond: assertion,
                                msg: "assertion".to_owned(),
                            });
                            return;
                        } else if is_spec(self.tcx(), *def_id) {
                            return;
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
                let e = Operand::Copy(self.translate_place(pl.as_ref()));
                RValue::Len(e)
            }
            Rvalue::Cast(CastKind::IntToInt | CastKind::PtrToPtr, op, cast_ty) => {
                let op_ty = op.ty(self.body, self.tcx());
                RValue::Cast(self.translate_operand(op), op_ty, *cast_ty)
            }
            Rvalue::Repeat(op, len) => RValue::Repeat(
                self.translate_operand(op),
                Operand::Constant(crate::constant::from_ty_const(
                    self.ctx,
                    *len,
                    self.ctx.types.usize,
                    self.param_env(),
                    si.span,
                )),
            ),

            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), op, ty) => {
                if let Some(t) = ty.builtin_deref(true)
                    && t.is_slice()
                {
                    // treat &[T; N] to &[T] casts as normal assignments
                    RValue::Operand(self.translate_operand(op))
                } else {
                    // TODO: Since we don't do anything with casts into `dyn` objects, just ignore them
                    return;
                }
            }
            Rvalue::Cast(
                CastKind::PointerCoercion(_)
                | CastKind::PointerExposeProvenance
                | CastKind::PointerWithExposedProvenance
                | CastKind::DynStar
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
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _) => self.ctx.crash_and_error(
                si.span,
                &format!("MIR code used an unsupported Rvalue {:?}", rvalue),
            ),
        };

        if !ty.is_unit() {
            self.emit_assignment(place, rval, span);
        }
    }

    fn compute_ref_place(&self, pl: Place<'tcx>, loc: Location) -> Place<'tcx> {
        let Some(borrows) = &self.borrows else { return pl };

        let dom = self.body.basic_blocks.dominators();
        let two_phase = borrows
            .local_map
            .get(&pl.local)
            .iter()
            .flat_map(|is| is.iter())
            .filter(|i| {
                let res_loc = borrows[**i].reserve_location;
                if res_loc.block == loc.block {
                    res_loc.statement_index <= loc.statement_index
                } else {
                    dom.dominates(res_loc.block, loc.block)
                }
            })
            .filter(|i| {
                if let TwoPhaseActivation::ActivatedAt(act_loc) = borrows[**i].activation_location {
                    if act_loc.block == loc.block {
                        loc.statement_index < act_loc.statement_index
                    } else {
                        dom.dominates(loc.block, act_loc.block)
                    }
                } else {
                    false
                }
            })
            .nth(0);

        if let Some(two_phase) = two_phase {
            let place = borrows[*two_phase].assigned_place.clone();
            self.ctx.mk_place_deref(place)
        } else {
            pl
        }
    }
}
