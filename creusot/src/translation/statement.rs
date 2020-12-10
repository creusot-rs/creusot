use rustc_errors::DiagnosticId;
use rustc_middle::mir::{
    BorrowKind::*, Operand::*, Place, Rvalue, SourceInfo, Statement, StatementKind,
};
use rustc_hir::def::Namespace;

use crate::{
    mlcfg::{
        // Constant,
        Exp::{self, *},
        Statement::*,
    },
    place::simplify_place,
    ts_to_symbol,
};

use super::{specification, util::spec_attrs, FunctionTranslator};

impl<'tcx> FunctionTranslator<'_, 'tcx> {
    pub fn translate_statement(&mut self, statement: &'_ Statement<'tcx>) {
        use StatementKind::*;
        match statement.kind {
            Assign(box (ref pl, ref rv)) => self.translate_assign(statement.source_info, pl, rv),
            SetDiscriminant { .. } => {
                // TODO: implement support for set discriminant
                self.sess.span_fatal_with_code(statement.source_info.span, "SetDiscriminant is not supported", DiagnosticId::Error(String::from("creusot")))
            }
            // Erase Storage markers and Nops
            StorageDead(_) | StorageLive(_) | Nop => {}
            // Not real instructions
            FakeRead(_, _) | AscribeUserType(_, _) | Retag(_, _) | Coverage(_) => {}
            // No assembly!
            LlvmInlineAsm(_) => self.sess.span_fatal_with_code(statement.source_info.span, "inline assembly is not supported", DiagnosticId::Error(String::from("creusot"))),
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
                Move(pl) | Copy(pl) => self.translate_rplace(&simplify_place(self.tcx, self.body, pl)),
                Constant(box c) => Const(crate::mlcfg::Constant::from_mir_constant(self.tcx, c)),
            },
            Rvalue::Ref(_, ss, pl) => {
                let rplace = simplify_place(self.tcx, self.body, pl);

                match ss {
                    Shared | Shallow | Unique => self.translate_rplace(&rplace),
                    Mut { .. } => {

                        self.emit_assignment(
                            &lplace,
                            BorrowMut(box self.translate_rplace(&rplace)),
                        );
                        self.emit_assignment(
                            &rplace,
                            Final(box self.translate_rplace(&lplace)),
                        );
                        return;
                    }
                }
            }
            // Rvalue::Discriminant(pl) => self.translate_rplace(&simplify_place(self.tcx, self.body, pl)),
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(op, l, r) | Rvalue::CheckedBinaryOp(op, l, r) => {
                BinaryOp((*op).into(), box self.translate_operand(l), box self.translate_operand(r))
            }
            Rvalue::Aggregate(box kind, ops) => {
                use rustc_middle::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op)).collect();

                match kind {
                    Tuple => Exp::Tuple(fields),
                    Adt(adt, varix, _, _, _) => {
                        let variant_def = &adt.variants[*varix];
                        let cons_name = (&variant_def.ident.name).to_string();

                        let mut path = super::translate_defid(self.tcx, adt.did, Namespace::TypeNS);
                        path.replace_name(cons_name);

                        Constructor { ctor: path, args: fields }
                    }
                    Closure(def_id, _) => {
                        let attrs = self.tcx.get_attrs(*def_id);

                        let mut spec_attrs = spec_attrs(attrs);

                        if spec_attrs.len() == 1 {
                            let attr = spec_attrs.remove(0);
                            if is_invariant_marker(attr) {
                                let inv = ts_to_symbol(attr.args.inner_tokens()).unwrap();

                                let inv_string =
                                    specification::invariant_to_why(self.body, si, inv);

                                self.emit_statement(Invariant(invariant_name(attr), Verbatim(inv_string)));
                                return;
                            } else {
                                self.sess.span_fatal_with_code(si.span, &format!("unexpected specification attribute {:?}", spec_attrs), DiagnosticId::Error(String::from("creusot")))
                            }
                        } else {
                            self.sess.span_fatal_with_code(si.span, "closures are not yet supported", DiagnosticId::Error(String::from("creusot")))
                        }
                    }
                    _ => {
                        self.sess.span_fatal_with_code(si.span, &format!("the rvalue {:?} is not currently supported", kind), DiagnosticId::Error("creusot".into()))
                    }
                }
            }

            Rvalue::Cast(_, _, _)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _)
            | Rvalue::Len(_) => self.sess.span_fatal_with_code(si.span, "MIR code used an unsupported Rvalue", DiagnosticId::Error(String::from("creusot"))),
        };

        self.emit_assignment(&lplace, rval);
    }
}

fn is_invariant_marker(attr: &rustc_ast::AttrItem) -> bool {
    attr.path.segments[2].ident.name.to_string() == "invariant"
}

fn invariant_name(attr: &rustc_ast::AttrItem) -> String {
    attr.path.segments[3].ident.name.to_string()
}
