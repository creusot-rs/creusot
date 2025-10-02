use super::BodyTranslator;
use crate::{
    contracts_items::{
        is_assertion, is_before_loop, is_erasure, is_invariant, is_snapshot_closure, is_spec,
        is_variant,
    },
    ctx::HasTyCtxt as _,
    translation::{
        fmir::{self, Operand, RValue},
        pearlite::Term,
    },
};
use rustc_ast::Mutability;
use rustc_middle::{
    mir::{
        BorrowKind::*, CastKind, Location, Operand::*, Place, Rvalue, SourceInfo, Statement,
        StatementKind,
    },
    ty::{ConstKind, Ty, TyKind, UintTy, adjustment::PointerCoercion},
};
use rustc_span::Span;

impl<'tcx> BodyTranslator<'_, 'tcx> {
    pub(super) fn translate_statement(&mut self, statement: &'_ Statement<'tcx>, loc: Location) {
        let si = statement.source_info;
        self.resolve_at(loc, si.span);
        self.activate_two_phase(loc, si.span);
        match statement.kind {
            StatementKind::Assign(box (pl, ref rv)) => {
                self.translate_assign(si, pl, rv, loc);
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
            | StatementKind::BackwardIncompatibleDropHint { .. } => {}
            StatementKind::SetDiscriminant { .. } => {
                self.crash_and_error(statement.source_info.span, "SetDiscriminant is not supported")
            }
            StatementKind::Intrinsic(_) => {
                self.crash_and_error(statement.source_info.span, "intrinsics are not supported")
            }
            StatementKind::Deinit(_) => unreachable!("Deinit unsupported"),
        }
    }

    fn translate_assign(
        &mut self,
        si: SourceInfo,
        place: Place<'tcx>,
        rvalue: &'_ Rvalue<'tcx>,
        loc: Location,
    ) {
        let ty = rvalue.ty(self.body, self.tcx());
        let span = si.span;
        let rval: RValue<'tcx> = match rvalue {
            Rvalue::Use(op) => match op {
                Move(_pl) | Copy(_pl) => RValue::Operand(self.translate_operand(op, span)),
                Constant(box c) => {
                    if let TyKind::Closure(def_id, _) = c.const_.ty().peel_refs().kind()
                        && is_snapshot_closure(self.tcx(), *def_id)
                    {
                        return;
                    };
                    RValue::Operand(self.translate_operand(op, span))
                }
            },
            &Rvalue::Ref(_, ss, pl) => match ss {
                Shared | Fake(..) => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }
                    RValue::Operand(Operand::Copy(self.translate_place(pl, span)))
                }
                // Special case to support const-promoted `&mut []`
                Mut { .. } if self.borrow_data.is_none() && is_mut_ref_empty(&ty) => {
                    self.emit_borrow(place, pl, fmir::BorrowKind::Mut, span);
                    // No need to resolve: the length of the final value is set to 0 by the type invariant
                    return;
                }
                Mut { .. } => {
                    let Some(borrow_data) = &self.borrow_data else { self.error_no_borrow_data() };
                    if self.erased_locals.contains(pl.local) || borrow_data.is_two_phase_at(loc) {
                        return;
                    }
                    let is_final = borrow_data.is_final_at(loc);
                    self.emit_borrow(place, pl, is_final, span);
                    return;
                }
            },
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(op, box (l, r)) => {
                RValue::BinOp(*op, self.translate_operand(l, span), self.translate_operand(r, span))
            }
            Rvalue::UnaryOp(op, v) => RValue::UnaryOp(*op, self.translate_operand(v, span)),
            Rvalue::Aggregate(box kind, ops) => {
                use rustc_middle::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op, span)).collect();

                match kind {
                    Tuple => RValue::Tuple(fields),
                    Adt(adt, varix, subst, _, _) => {
                        let variant = self.ctx.adt_def(*adt).variant(*varix).def_id;
                        RValue::Constructor(variant, subst, fields)
                    }
                    Closure(def_id, subst) => {
                        if is_variant(self.tcx(), *def_id) || is_before_loop(self.tcx(), *def_id) {
                            return;
                        } else if is_invariant(self.tcx(), *def_id) {
                            match self.invariant_assertions.remove(def_id) {
                                None => return,
                                Some((cond, msg)) => {
                                    self.emit_statement(fmir::Statement {
                                        kind: fmir::StatementKind::Assertion {
                                            cond,
                                            msg,
                                            trusted: false,
                                        },
                                        span,
                                    });
                                    return;
                                }
                            }
                        } else if is_assertion(self.tcx(), *def_id) {
                            let assertion = self
                                .assertions
                                .remove(def_id)
                                .expect("Could not find body of assertion");
                            self.emit_statement(fmir::Statement {
                                kind: fmir::StatementKind::Assertion {
                                    cond: assertion,
                                    msg: "expl:assertion".to_owned(),
                                    trusted: false,
                                },
                                span,
                            });
                            return;
                        } else if is_spec(self.tcx(), *def_id) || is_erasure(self.tcx(), *def_id) {
                            return;
                        } else {
                            RValue::Constructor(*def_id, subst, fields)
                        }
                    }
                    Array(_) => RValue::Array(fields),
                    _ => self.crash_and_error(
                        si.span,
                        format!("the rvalue {:?} is not currently supported", kind),
                    ),
                }
            }
            Rvalue::Cast(CastKind::IntToInt | CastKind::PtrToPtr, op, cast_ty) => {
                let op_ty = op.ty(self.body, self.tcx());
                RValue::Cast(self.translate_operand(op, span), op_ty, *cast_ty)
            }
            Rvalue::Repeat(op, len) => RValue::Repeat(
                self.translate_operand(op, span),
                Operand::Term(Term::const_(*len, Ty::new_uint(self.tcx(), UintTy::Usize), si.span)),
            ),
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, _), op, ty) => {
                let Some(t) = ty.builtin_deref(true) else {
                    self.crash_and_error(
                        si.span,
                        format!("unsupported cast from {} to {}", op.ty(self.body, self.tcx()), ty),
                    )
                };
                if t.is_slice() {
                    // treat &[T; N] to &[T] casts as normal assignments
                    RValue::Operand(self.translate_operand(op, span))
                } else {
                    RValue::Cast(
                        self.translate_operand(op, span),
                        op.ty(self.body, self.tcx()),
                        *ty,
                    )
                }
            }
            &Rvalue::RawPtr(_, pl) => RValue::Ptr(self.translate_place(pl, span)),
            Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _),
                op,
                _,
            ) => RValue::Operand(self.translate_operand(op, span)),
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
            ) => self.ctx.crash_and_error(si.span, format!("Unsupported pointer cast: {rvalue:?}")),
            Rvalue::CopyForDeref(_)
            | Rvalue::ShallowInitBox(_, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::WrapUnsafeBinder(_, _) => self.ctx.crash_and_error(
                si.span,
                format!("MIR code used an unsupported Rvalue {:?}", rvalue),
            ),
        };

        if !ty.is_unit() {
            self.emit_assignment(place, rval, span);
        }
    }

    pub(super) fn activate_two_phase(&mut self, loc: Location, span: Span) {
        let Some(borrow_data) = &mut self.borrow_data else {
            return;
        };
        for (lhs, rhs, is_final) in borrow_data.remove_two_phase_activated_at(loc) {
            self.emit_borrow(lhs, rhs, is_final, span)
        }
    }

    /// Fail if mutable borrows are used and no borrow data is available.
    fn error_no_borrow_data(&self) -> ! {
        self.crash_and_error(
            self.body.span,
            format!(
                "can't translate {}: no data to resolve mutable borrows",
                self.tcx().def_path_str(self.body_id.def_id)
            ),
        );
    }
}

/// Check whether `ty` is of the form `&mut [T; 0]`
fn is_mut_ref_empty<'tcx>(ty: &Ty<'tcx>) -> bool {
    let TyKind::Ref(_, ty, Mutability::Mut) = ty.kind() else {
        return false;
    };
    let TyKind::Array(_, len) = ty.kind() else {
        return false;
    };
    let ConstKind::Value(value) = len.kind() else {
        return false;
    };
    let Some(scalar) = value.valtree.try_to_scalar_int() else {
        return false;
    };
    scalar.is_null()
}
