use rustc_middle::mir::{
    BorrowKind::*, Operand::*, Place, Rvalue, SourceInfo, Statement, StatementKind,
};

use why3::mlcfg::{
    // Constant,
    Exp::{self, *},
    Statement::*,
};

use super::specification::Spec;
use super::{specification, FunctionTranslator};

impl<'tcx> FunctionTranslator<'_, '_, 'tcx> {
    pub fn translate_statement(&mut self, statement: &'_ Statement<'tcx>) {
        use StatementKind::*;
        match statement.kind {
            Assign(box (ref pl, ref rv)) => self.translate_assign(statement.source_info, pl, rv),
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
            // No assembly!
            LlvmInlineAsm(_) => self
                .ctx
                .crash_and_error(statement.source_info.span, "inline assembly is not supported"),
        }
    }

    fn translate_assign(
        &mut self,
        si: SourceInfo,
        place: &'_ Place<'tcx>,
        rvalue: &'_ Rvalue<'tcx>,
    ) {
        let rval = match rvalue {
            Rvalue::Use(rval) => match rval {
                Move(pl) | Copy(pl) => {
                    // TODO: should this be done for *any* form of assignment?
                    let ty = place.ty(self.body, self.tcx).ty;
                    let pl_exp = self.translate_rplace(&place);
                    let assumption: Exp =
                        super::ty::drop_predicate(&mut self.ctx, ty).app_to(pl_exp);
                    self.emit_statement(Assume(assumption));
                    self.translate_rplace(pl)
                }
                Constant(box c) => Const(super::from_mir_constant(self.tcx, c)),
            },
            Rvalue::Ref(_, ss, pl) => match ss {
                Shared | Shallow | Unique => self.translate_rplace(&pl),
                Mut { .. } => {
                    let borrow = BorrowMut(box self.translate_rplace(&pl));
                    self.emit_assignment(&place, borrow);
                    let reassign = Final(box self.translate_rplace(&place));
                    self.emit_assignment(&pl, reassign);
                    return;
                }
            },
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(op, box (l, r)) | Rvalue::CheckedBinaryOp(op, box (l, r)) => BinaryOp(
                binop_to_binop(*op),
                box self.translate_operand(l),
                box self.translate_operand(r),
            ),
            Rvalue::Aggregate(box kind, ops) => {
                use rustc_middle::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op)).collect();

                match kind {
                    Tuple => Exp::Tuple(fields),
                    Adt(adt, varix, _, _, _) => {
                        let variant_def = &adt.variants[*varix];
                        let qname = super::translate_value_id(self.tcx, variant_def.def_id);

                        Constructor { ctor: qname, args: fields }
                    }
                    Closure(def_id, _) => {
                        let attrs = self.tcx.get_attrs(*def_id);

                        match specification::spec_kind(attrs) {
                            Ok(Spec::Invariant { name, expression }) => {
                                let invariant = specification::invariant_to_why(
                                    &self.resolver,
                                    &mut self.ctx,
                                    self.body,
                                    si,
                                    expression,
                                );

                                self.imports.extend(
                                    invariant.qfvs().into_iter().map(|qn| qn.module_name()),
                                );

                                self.emit_statement(Invariant(name, invariant));
                                return;
                            }
                            Ok(_) => {
                                self.ctx.crash_and_error(si.span, "closures are not yet supported")
                            }
                            Err(err) => self.ctx.crash_and_error(si.span, &format!("{:?}", err)),
                        }
                    }
                    _ => self.ctx.crash_and_error(
                        si.span,
                        &format!("the rvalue {:?} is not currently supported", kind),
                    ),
                }
            }
            Rvalue::UnaryOp(op, v) => UnaryOp(unop_to_unop(*op), box self.translate_operand(v)),
            Rvalue::Len(pl) => {
                RecField { record: box self.translate_rplace(&pl), label: "length".into() }
            }
            Rvalue::Cast(_, _, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _) => self.ctx.crash_and_error(
                si.span,
                &format!("MIR code used an unsupported Rvalue {:?}", rvalue),
            ),
        };

        self.emit_assignment(place, rval);
    }
}

fn unop_to_unop(op: rustc_middle::mir::UnOp) -> why3::mlcfg::UnOp {
    match op {
        rustc_middle::mir::UnOp::Not => why3::mlcfg::UnOp::Not,
        rustc_middle::mir::UnOp::Neg => why3::mlcfg::UnOp::Neg,
    }
}

fn binop_to_binop(op: rustc_middle::mir::BinOp) -> why3::mlcfg::BinOp {
    use rustc_middle::mir;
    use why3::mlcfg::BinOp;
    match op {
        mir::BinOp::Add => BinOp::Add,
        mir::BinOp::Sub => BinOp::Sub,
        mir::BinOp::Mul => BinOp::Mul,
        mir::BinOp::Div => BinOp::Div,
        mir::BinOp::Eq => BinOp::Eq,
        mir::BinOp::Lt => BinOp::Lt,
        mir::BinOp::Le => BinOp::Le,
        mir::BinOp::Gt => BinOp::Gt,
        mir::BinOp::Ge => BinOp::Ge,
        mir::BinOp::Ne => BinOp::Ne,
        _ => unimplemented!("unsupported binary operation: {:?}", op),
    }
}
