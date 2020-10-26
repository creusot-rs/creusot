use rustc_hir::{def::CtorKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;

use crate::place::{MirPlace, Projection::*, Mutability::*};

use crate::whycfg::{*, MlCfgExp::*, MlCfgPattern::*, MlCfgStatement::*};

mod terminator;
mod ty;

pub struct TranslationCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> TranslationCtx<'tcx> {
    fn translate_defid(&self, def_id: DefId) -> String {
      self.tcx.def_path_str(def_id)
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
            Deref(Mut) => {
                inner = RecUp {
                    record: box rhs_to_why_exp(&stump),
                    label: "current".into(),
                    val: box inner,
                }
            }
            Deref(Not) => {
                // Immutable references are erased in MLCFG
            }
            FieldAccess { ctor, ix, size, field, kind } => match kind {
                CtorKind::Fn => {
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
                CtorKind::Const => unimplemented!(),
                CtorKind::Fictive => {
                    inner = RecUp {
                        record: box rhs_to_why_exp(&stump),
                        label: field.to_string(),
                        val: box inner,
                    }
                }
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

    return Assign { lhs: lhs.local, rhs: inner};
}

// [(P as Some)]   ---> [_1]
// [(P as Some).0] ---> let Some(a) = [_1] in a
// [(* P)] ---> * [P]
pub fn rhs_to_why_exp(rhs: &MirPlace) -> MlCfgExp {
    let mut inner = Local(rhs.local);

    for proj in rhs.proj.iter() {
        match proj {
            Deref(Mut) => {
                inner = Current(box inner);
            }
            Deref(Not) => {
                // Immutable references are erased in MLCFG
            }
            FieldAccess { ctor, ix, size, field, kind } => {
                match kind {
                    // Tuple
                    CtorKind::Fn => {
                        let mut pat = vec![Wildcard; *ix];
                        pat.push(VarP("a".into()));
                        pat.append(&mut vec![Wildcard; size - ix - 1]);

                        inner = Let {
                            pattern: ConsP(ctor.to_string(), pat),
                            arg: box inner,
                            body: box Var("a".into()),
                        }
                    }
                    // Unit
                    CtorKind::Const => {
                        assert!(*size == 1 && *ix == 0);
                        unimplemented!();
                    }
                    // Struct
                    CtorKind::Fictive => {
                        inner = RecField { rec: box inner, field: field.name.to_string() }

                        // Let {
                        //     pattern: RecP(field.name.to_string(), "a".into()),
                        //     arg: box inner,
                        //     body: box Var("a".into()),
                        // }
                    }
                }
            }
            TupleAccess { size, ix } => {
                let mut pat = vec![Wildcard; *ix];
                pat.push(VarP("a".into()));
                pat.append(&mut vec![Wildcard; size - ix - 1]);

                inner = Let { pattern: TupleP(pat), arg: box inner, body: box Var("a".into()) }
            }
        }
    }
    return inner;
}
