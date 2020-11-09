use rustc_hir::def::CtorKind;
use rustc_middle::mir::{BorrowKind::*, Operand::*, Place, Rvalue, SourceInfo, Statement, StatementKind};

use crate::{Projection::*, mlcfg::{
        MlCfgConstant,
        MlCfgExp::{self, *},
        MlCfgPattern::*,
        MlCfgStatement::{self, *},
    }, place::from_place, place::{MirPlace, Mutability as M}, ts_to_symbol};

use super::{FunctionTranslator, rhs_to_why_exp, util::spec_attrs, specification};

impl<'tcx> FunctionTranslator<'_, 'tcx> {
    pub fn translate_statement(&mut self, statement: &'_ Statement<'tcx>) {
        if let StatementKind::Assign(box (ref pl, ref rv)) = statement.kind {
            self.translate_assign(statement.source_info, pl, rv)
        }
    }

    fn translate_assign(&mut self, si: SourceInfo, place: &'_ Place<'tcx>, rvalue: &'_ Rvalue<'tcx>) {
        let lplace = from_place(self.tcx, self.body, place);
        let rval = match rvalue {
            Rvalue::Use(rval) => match rval {
                Move(pl) | Copy(pl) => rhs_to_why_exp(&from_place(self.tcx, self.body, pl)),
                Constant(box c) => Const(MlCfgConstant::from_mir_constant(self.tcx, c)),
            },
            Rvalue::Ref(_, ss, pl) => {
                let rplace = from_place(self.tcx, self.body, pl);
                match ss {
                    Shared | Shallow | Unique => rhs_to_why_exp(&rplace),
                    Mut { .. } => {
                        self.emit_statement(create_assign(
                            &lplace,
                            BorrowMut(box rhs_to_why_exp(&rplace)),
                        ));
                        self.emit_statement(create_assign(
                            &rplace,
                            Final(box rhs_to_why_exp(&lplace)),
                        ));
                        return;
                    }
                }
            }
            // Rvalue::Discriminant(pl) => rhs_to_why_exp(&from_place(self.tcx, self.body, pl)),
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(op, l, r) | Rvalue::CheckedBinaryOp(op, l, r) => {
                BinaryOp(*op, box self.translate_operand(l), box self.translate_operand(r))
            }
            Rvalue::Aggregate(box kind, ops) => {
                use rustc_middle::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op)).collect();

                match kind {
                    Tuple => MlCfgExp::Tuple(fields),
                    Adt(adt, varix, _, _, _) => {
                        let variant_def = &adt.variants[*varix];
                        let cons_name = variant_def.ident.to_string();

                        Constructor { ctor: cons_name, args: fields }
                    }
                    Array(_) => unimplemented!("array"),
                    Closure(def_id, _) => {
                        let attrs = self.tcx.get_attrs(*def_id);

                        let mut spec_attrs = spec_attrs(attrs);

                        if spec_attrs.len() == 1 {
                            let attr = spec_attrs.remove(0);
                            match attr.path.segments[2].ident.name.to_string().as_ref() {
                                "invariant" => {
                                    let inv = ts_to_symbol(attr.args.inner_tokens());

                                    let inv_string = specification::invariant_to_why(self.body, si, inv);

                                    self.emit_statement(Invariant(Verbatim(inv_string)));
                                    return;
                                }
                                a => { panic!("unknown kind of specification marker: {}",a)}
                            }
                        } else {
                            unimplemented!("support for program closures isn't implemented");
                        }
                    }
                    Generator(_, _, _) => unimplemented!("{:?}", kind),
                }
            }

            Rvalue::Cast(_, _, _)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _)
            | Rvalue::Len(_) => unimplemented!("{:?}", rvalue),
        };

        let mlstmt = create_assign(&lplace, rval);
        self.emit_statement(mlstmt);
    }
}

/// Correctly translate an assignment from one place to another. The challenge here is correctly
/// construction the expression that assigns deep inside a structure.
/// (_1 as Some) = P      ---> let _1 = P ??
/// (*_1) = P             ---> let _1 = { current = P, .. }
/// (_1.2) = P            ---> let _1 = { _1 with [[2]] = P } (struct)
///                       ---> let _1 = (let Cons(a, b, c) = _1 in Cons(a, b, P)) (tuple)
/// (*_1).1 = P           ---> let _1 = { _1 with current = ({ * _1 with [[1]] = P })}
/// ((*_1) as Some).0 = P ---> let _1 = { _1 with current = (let Some(X) = _1 in Some(P) )}

/// [(_1 as Some).0] = X   ---> let _1 = (let Some(a) = _1 in Some(X))
/// (* (* _1).2) = X ---> let _1 = { _1 with current = { * _1 with current = [(**_1).2 = X] }}
pub fn create_assign(lhs: &MirPlace, rhs: MlCfgExp) -> MlCfgStatement {
    // Translation happens inside to outside, which means we scan projection elements in reverse
    // building up the inner expression. We start with the RHS expression which is at the deepest
    // level.
    let mut inner = rhs;
    // The stump represents the projection up to the element being translated
    let mut stump = lhs.clone();
    for proj in lhs.proj.iter().rev() {
        // Remove the last element from the projection
        stump.proj.pop();

        match proj {
            Deref(M::Mut) => {
                inner = RecUp {
                    record: box rhs_to_why_exp(&stump),
                    label: "current".into(),
                    val: box inner,
                }
            }
            Deref(M::Not) => {
                // Immutable references are erased in MLCFG
            }
            FieldAccess { ctor, ix, size, kind, .. } => match kind {
                CtorKind::Fn | CtorKind::Fictive => {
                    let varpats = ('a'..).map(|c| VarP(c.to_string())).take(*size).collect();
                    let mut varexps: Vec<MlCfgExp> =
                        ('a'..).map(|c| Var(c.to_string())).take(*size).collect();
                    varexps[*ix] = inner;

                    inner = Let {
                        pattern: ConsP(ctor.to_string(), varpats),
                        arg: box rhs_to_why_exp(&stump),
                        body: box Constructor { ctor: ctor.to_string(), args: varexps },
                    }
                }
                CtorKind::Const => inner = Constructor { ctor: ctor.to_string(), args: vec![] },
            },
            TupleAccess { size, ix } => {
                let varpats = ('a'..).map(|c| VarP(c.to_string())).take(*size).collect();
                let mut varexps: Vec<_> = ('a'..).map(|c| Var(c.to_string())).take(*size).collect();
                varexps[*ix] = inner;

                inner = Let {
                    pattern: TupleP(varpats),
                    arg: box rhs_to_why_exp(&stump),
                    body: box Tuple(varexps),
                }
            }
        }
    }

    Assign { lhs: lhs.local, rhs: inner }
}
