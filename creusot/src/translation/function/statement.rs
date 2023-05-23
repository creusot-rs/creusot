use borrowck::borrow_set::TwoPhaseActivation;
use rustc_middle::{
    mir::{
        BinOp, BorrowKind::*, CastKind, Location, Operand::*, Place, Rvalue, SourceInfo, Statement,
        StatementKind,
    },
    ty::adjustment::PointerCast,
};

use super::BodyTranslator;
use crate::{
    translation::fmir::{self, Expr, RValue},
    util::{self, is_ghost_closure},
};

impl<'tcx> BodyTranslator<'_, 'tcx> {
    pub(crate) fn translate_statement(&mut self, statement: &'_ Statement<'tcx>, loc: Location) {
        let mut resolved_during = self.resolver.resolved_locals_during(loc);

        use StatementKind::*;
        match statement.kind {
            Assign(box (ref pl, ref rv)) => {
                self.translate_assign(statement.source_info, pl, rv, loc);

                // if the lhs local becomes resolved during the assignment,
                // we cannot resolve it afterwards.
                if !pl.is_indirect() {
                    resolved_during.remove(pl.local);
                }
            }
            SetDiscriminant { .. } => {
                // TODO: implement support for set discriminant
                self.ctx
                    .crash_and_error(statement.source_info.span, "SetDiscriminant is not supported")
            }
            // Erase Storage markers and Nops
            StorageDead(_) | StorageLive(_) | Nop => {}
            // Not real instructions
            FakeRead(_) | AscribeUserType(_, _) | Retag(_, _) | Coverage(_) => {}
            Intrinsic(_) => {
                self.ctx.crash_and_error(statement.source_info.span, "intrinsics are not supported")
            }
            Deinit(_) => unreachable!("Deinit unsupported"),
            PlaceMention(_) => {}
            ConstEvalCounter => {}
            // No assembly!
            // LlvmInlineAsm(_) => self
            //     .ctx
            //     .crash_and_error(statement.source_info.span, "inline assembly is not supported"),
        }

        self.resolve_locals(resolved_during);
    }

    fn translate_assign(
        &mut self,
        si: SourceInfo,
        place: &'_ Place<'tcx>,
        rvalue: &'_ Rvalue<'tcx>,
        loc: Location,
    ) {
        let rval: Expr<'tcx> = match rvalue {
            Rvalue::Use(rval) => match rval {
                Move(pl) => Expr::Move(*pl),
                Copy(pl) => Expr::Copy(*pl),
                Constant(box c) => {
                    if is_ghost_closure(self.tcx, c.literal.ty()).is_some() {
                        return;
                    };
                    crate::constant::from_mir_constant(self.param_env(), self.ctx, c)
                }
            },
            Rvalue::Ref(_, ss, pl) => match ss {
                Shared | Shallow | Unique => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }

                    Expr::Place(self.compute_ref_place(*pl, loc))
                }
                Mut { .. } => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }

                    self.emit_borrow(place, pl);
                    return;
                }
            },
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(BinOp::BitAnd, box (l, _)) if !l.ty(self.body, self.tcx).is_bool() => {
                self.ctx.crash_and_error(si.span, "bitwise operations are currently unsupported")
            }
            Rvalue::BinaryOp(op, box (l, r)) | Rvalue::CheckedBinaryOp(op, box (l, r)) => {
                let exp = Expr::BinOp(
                    *op,
                    l.ty(self.body, self.tcx),
                    Box::new(self.translate_operand(l)),
                    Box::new(self.translate_operand(r)),
                );
                Expr::Span(si.span, Box::new(exp))
            }
            Rvalue::UnaryOp(op, v) => {
                Expr::UnaryOp(*op, v.ty(self.body, self.tcx), Box::new(self.translate_operand(v)))
            }
            Rvalue::Aggregate(box kind, ops) => {
                use rustc_middle::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op)).collect();

                match kind {
                    Tuple => Expr::Tuple(fields),
                    Adt(adt, varix, subst, _, _) => {
                        // self.ctx.translate(*adt);
                        let variant = self.tcx.adt_def(*adt).variant(*varix).def_id;

                        Expr::Constructor(variant, subst, fields)
                    }
                    Closure(def_id, subst) => {
                        if util::is_invariant(self.tcx, *def_id)
                            || util::is_variant(self.tcx, *def_id)
                        {
                            return;
                        } else if util::is_assertion(self.tcx, *def_id) {
                            let assertion = self
                                .assertions
                                .remove(def_id)
                                .expect("Could not find body of assertion");
                            self.emit_statement(fmir::Statement::Assertion(assertion));
                            return;
                        } else if util::is_ghost(self.tcx, *def_id) {
                            return;
                        } else if util::is_spec(self.tcx, *def_id) {
                            return;
                        } else {
                            Expr::Constructor(*def_id, subst, fields)
                        }
                    }
                    Array(_) => Expr::Array(fields),
                    _ => self.ctx.crash_and_error(
                        si.span,
                        &format!("the rvalue {:?} is not currently supported", kind),
                    ),
                }
            }
            Rvalue::Len(pl) => Expr::Len(Box::new(Expr::Place(*pl))),
            Rvalue::Cast(CastKind::IntToInt | CastKind::PtrToPtr, op, ty) => {
                let op_ty = op.ty(self.body, self.tcx);
                Expr::Cast(Box::new(self.translate_operand(op)), op_ty, *ty)
            }
            Rvalue::Repeat(op, len) => Expr::Repeat(
                Box::new(self.translate_operand(op)),
                Box::new(crate::constant::from_ty_const(self.ctx, *len, self.param_env(), si.span)),
            ),
            Rvalue::Cast(CastKind::Pointer(PointerCast::Unsize), op, ty) => {
                if let Some(t) = ty.builtin_deref(true) && t.ty.is_slice() {
                    // treat &[T; N] to &[T] casts as normal assignments
                    self.translate_operand(op)
                } else {
                    // TODO: Since we don't do anything with casts into `dyn` objects, just ignore them
                    return;
                }
            }
            Rvalue::Cast(
                CastKind::Pointer(_)
                | CastKind::PointerExposeAddress
                | CastKind::PointerFromExposedAddress
                | CastKind::DynStar
                | CastKind::IntToFloat
                | CastKind::FloatToInt
                | CastKind::FnPtrToPtr
                | CastKind::FloatToFloat,
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

        // if the lhs place is resolved during computation of the rhs
        // split the assignment and resolve the local inbetween
        let mut live_before = self.resolver.live_locals_before(loc);
        live_before.union(&self.resolver.frozen_locals_before(loc));

        let lhs_ty = place.ty(self.body, self.tcx).ty;
        if !place.is_indirect() && live_before.contains(place.local)
            && let Some((id, subst)) = super::resolve_predicate_of(self.ctx, self.param_env(), lhs_ty) {
            let tmp_local: Place = self.fresh_local(lhs_ty).into();
            self.emit_assignment(&tmp_local, RValue::Expr(rval));

            if let Some((id, substs)) = self.ctx.type_invariant(self.body_id.def_id(), lhs_ty) {
                self.emit_statement(fmir::Statement::AssertTyInv(id, substs, *place));
            }

            self.emit_statement(fmir::Statement::Resolve(id, subst, *place));

            self.emit_assignment(place, RValue::Expr(Expr::Place(tmp_local)));
        } else {
            self.emit_assignment(place, RValue::Expr(rval));
        }

        // Check if the local is a zombie:
        // if lhs local is dead after the assignment, emit resolve
        let dead_after = self.resolver.dead_locals_after(loc);
        if dead_after.contains(place.local) {
            self.emit_resolve(*place);
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
