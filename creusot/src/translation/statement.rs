use rustc_errors::DiagnosticId;
use rustc_middle::mir::{
    BorrowKind::*, Operand::*, Place, Rvalue, SourceInfo, Statement, StatementKind,
};

use why3::mlcfg::{
        // Constant,
        Exp::{self, *},
        Statement::*,
    };
use crate::{

    place::simplify_place,
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
                self.sess.span_fatal_with_code(
                    statement.source_info.span,
                    "SetDiscriminant is not supported",
                    DiagnosticId::Error(String::from("creusot")),
                )
            }
            // Erase Storage markers and Nops
            StorageDead(_) | StorageLive(_) | Nop => {}
            // Not real instructions
            FakeRead(_, _) | AscribeUserType(_, _) | Retag(_, _) | Coverage(_) => {}
            // No assembly!
            LlvmInlineAsm(_) => self.sess.span_fatal_with_code(
                statement.source_info.span,
                "inline assembly is not supported",
                DiagnosticId::Error(String::from("creusot")),
            ),
        }
    }

    fn translate_assign(
        &mut self,
        si: SourceInfo,
        place: &'_ Place<'tcx>,
        rvalue: &'_ Rvalue<'tcx>,
    ) {
        let lplace = simplify_place(self.tcx, self.body, place);
        let rval = match rvalue {
            Rvalue::Use(rval) => match rval {
                Move(pl) | Copy(pl) => {
                    self.translate_rplace(&simplify_place(self.tcx, self.body, pl))
                }
                Constant(box c) => Const(super::from_mir_constant(self.tcx, c)),
            },
            Rvalue::Ref(_, ss, pl) => {
                let rplace = simplify_place(self.tcx, self.body, pl);

                match ss {
                    Shared | Shallow | Unique => self.translate_rplace(&rplace),
                    Mut { .. } => {
                        let borrow = BorrowMut(box self.translate_rplace(&rplace));
                        self.emit_assignment(&lplace, borrow);
                        let reassign = Final(box self.translate_rplace(&lplace));
                        self.emit_assignment(&rplace, reassign);
                        return;
                    }
                }
            }
            // Rvalue::Discriminant(pl) => self.translate_rplace(&simplify_place(self.tcx, self.body, pl)),
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(op, l, r) | Rvalue::CheckedBinaryOp(op, l, r) => {
                BinaryOp(binop_to_binop(*op), box self.translate_operand(l), box self.translate_operand(r))
            }
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
                                    &mut self.ty_ctx,
                                    self.body,
                                    si,
                                    expression,
                                );
                                self.emit_statement(Invariant(name, Verbatim(invariant)));
                                return;
                            }
                            Ok(_) => self.sess.span_fatal_with_code(
                                si.span,
                                "closures are not yet supported",
                                DiagnosticId::Error(String::from("creusot")),
                            ),
                            Err(err) => self.sess.span_fatal_with_code(
                                si.span,
                                &format!("{:?}", err),
                                DiagnosticId::Error(String::from("creusot")),
                            ),
                        }
                    }
                    _ => self.sess.span_fatal_with_code(
                        si.span,
                        &format!("the rvalue {:?} is not currently supported", kind),
                        DiagnosticId::Error("creusot".into()),
                    ),
                }
            }
            Rvalue::UnaryOp(op, v) => UnaryOp(unop_to_unop(*op), box self.translate_operand(v)),
            Rvalue::Len(pl) => {
                RecField { record: box self.translate_rplace(&simplify_place(self.tcx, self.body, pl)), label: "length".into() }
            }
            Rvalue::Cast(_, _, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _) => self.sess.span_fatal_with_code(
                si.span,
                &format!("MIR code used an unsupported Rvalue {:?}", rvalue),
                DiagnosticId::Error(String::from("creusot")),
            ),
        };

        self.emit_assignment(&lplace, rval);
    }
}

fn unop_to_unop(op: rustc_middle::mir::UnOp) -> why3::mlcfg::UnOp {
    match op {
        rustc_middle::mir::UnOp::Not => why3::mlcfg::UnOp::Not,
        rustc_middle::mir::UnOp::Neg => why3::mlcfg::UnOp::Neg,
    }
}

fn binop_to_binop(op: rustc_middle::mir::BinOp) -> why3::mlcfg::BinOp {
    use rustc_middle::mir; use why3::mlcfg::BinOp;
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
