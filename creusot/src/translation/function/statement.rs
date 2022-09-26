use creusot_rustc::{
    borrowck::borrow_set::TwoPhaseActivation,
    smir::mir::{
        BinOp, BorrowKind::*, CastKind, Location, Operand::*, Place, Rvalue, SourceInfo, Statement,
        StatementKind,
    },
};

use super::BodyTranslator;
use crate::{
    translation::fmir::{self, Expr, RValue},
    util::{self, is_ghost_closure},
};

impl<'tcx> BodyTranslator<'_, 'tcx> {
    pub(crate) fn translate_statement(&mut self, statement: &'_ Statement<'tcx>, loc: Location) {
        use StatementKind::*;
        match statement.kind {
            Assign(box (ref pl, ref rv)) => {
                self.translate_assign(statement.source_info, pl, rv, loc)
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
            CopyNonOverlapping(_) => self.ctx.crash_and_error(
                statement.source_info.span,
                "copy non overlapping is not supported",
            ),
            Deinit(_) => unreachable!("Deinit unsupported")
            // No assembly!
            // LlvmInlineAsm(_) => self
            //     .ctx
            //     .crash_and_error(statement.source_info.span, "inline assembly is not supported"),
        }
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
                Move(pl) => {
                    self.emit_statement(fmir::Statement::Resolve(*place));
                    Expr::Move(*pl)
                }
                Copy(pl) => {
                    self.emit_statement(fmir::Statement::Resolve(*place));
                    Expr::Copy(*pl)
                }
                Constant(box c) => {
                    if let Some(c) = c.literal.const_for_ty() {
                        if is_ghost_closure(self.tcx, c.ty()).is_some() {
                            return;
                        }
                    };
                    crate::constant::from_mir_constant(self.param_env(), self.ctx, c)
                }
            },
            Rvalue::Ref(_, ss, pl) => match ss {
                Shared | Shallow | Unique => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }

                    let dom = self.body.basic_blocks.dominators();
                    let two_phase = self
                        .borrows
                        .local_map
                        .get(&pl.local)
                        .iter()
                        .flat_map(|is| is.iter())
                        .filter(|i| {
                            let res_loc = self.borrows[**i].reserve_location;
                            if res_loc.block == loc.block {
                                res_loc.statement_index <= loc.statement_index
                            } else {
                                dom.is_dominated_by(loc.block, res_loc.block)
                            }
                        })
                        .filter(|i| {
                            if let TwoPhaseActivation::ActivatedAt(act_loc) =
                                self.borrows[**i].activation_location
                            {
                                if act_loc.block == loc.block {
                                    loc.statement_index < act_loc.statement_index
                                } else {
                                    dom.is_dominated_by(act_loc.block, loc.block)
                                }
                            } else {
                                false
                            }
                        })
                        .nth(0);
                    if let Some(two_phase) = two_phase {
                        let place = self.borrows[*two_phase].assigned_place.clone();
                        Expr::Place(self.ctx.mk_place_deref(place))
                    } else {
                        Expr::Place(*pl)
                    }
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
                    box self.translate_operand(l),
                    box self.translate_operand(r),
                );
                Expr::Span(si.span, box exp)
            }
            Rvalue::UnaryOp(op, v) => Expr::UnaryOp(*op, box self.translate_operand(v)),
            Rvalue::Aggregate(box kind, ops) => {
                use creusot_rustc::smir::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op)).collect();

                match kind {
                    Tuple => Expr::Tuple(fields),
                    Adt(adt, varix, subst, _, _) => {
                        self.ctx.translate(*adt);
                        let variant = self.tcx.adt_def(*adt).variant(*varix).def_id;

                        Expr::Constructor(variant, subst, fields)
                    }
                    Closure(def_id, subst) => {
                        let def_id = def_id.to_def_id();
                        if util::is_invariant(self.tcx, def_id) {
                            return;
                        } else if util::is_assertion(self.tcx, def_id) {
                            let assertion = self
                                .assertions
                                .remove(&def_id)
                                .expect("Could not find body of assertion");
                            self.emit_statement(fmir::Statement::Assertion(assertion));
                            return;
                        } else if util::is_ghost(self.tcx, def_id) {
                            return;
                        } else if util::is_spec(self.tcx, def_id) {
                            return;
                        } else {
                            Expr::Constructor(def_id, subst, fields)
                        }
                    }
                    _ => self.ctx.crash_and_error(
                        si.span,
                        &format!("the rvalue {:?} is not currently supported", kind),
                    ),
                }
            }
            Rvalue::Len(pl) => Expr::Len(box Expr::Place(*pl)),
            Rvalue::Cast(CastKind::Misc, op, ty) => {
                let op_ty = op.ty(self.body, self.tcx);
                Expr::Cast(box self.translate_operand(op), op_ty, *ty)
            }
            Rvalue::Cast(
                CastKind::Pointer(_)
                | CastKind::PointerExposeAddress
                | CastKind::PointerFromExposedAddress,
                _,
                _,
            ) => self.ctx.crash_and_error(si.span, "Pointer casts are currently unsupported"),
            Rvalue::CopyForDeref(_) => panic!(),
            Rvalue::ShallowInitBox(_, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _) => self.ctx.crash_and_error(
                si.span,
                &format!("MIR code used an unsupported Rvalue {:?}", rvalue),
            ),
        };
        self.emit_assignment(place, RValue::Expr(rval));
    }
}
