use crate::{backend::Namer, ctx::PreMod, fmir::Place, naming::ident_of};
use rustc_middle::{
    mir::{self, ProjectionElem, tcx::PlaceTy},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::Symbol;
use std::{cell::RefCell, iter::repeat_n, rc::Rc};
use why3::{
    Ident,
    coma::{Arg, Param},
    exp::{
        Exp::{self, *},
        Pattern::*,
    },
};

use super::program::{IntermediateStmt, LoweringState};

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
pub(crate) fn create_assign_inner<'tcx, N: Namer<'tcx>>(
    lower: &LoweringState<'_, 'tcx, N>,
    lhs: &Place<'tcx>,
    rhs: Exp,
    istmts: &mut Vec<IntermediateStmt>,
) {
    let rhs = lplace_to_expr(lower, lhs, rhs, istmts);
    istmts.push(IntermediateStmt::Assign(Ident::build(lhs.local.as_str()), rhs));
}

#[derive(Clone)]
pub(crate) struct Focus<'a>(Rc<RefCell<Box<dyn FnOnce(&mut Vec<IntermediateStmt>) -> Exp + 'a>>>);

impl<'a> Focus<'a> {
    pub(crate) fn new(f: impl FnOnce(&mut Vec<IntermediateStmt>) -> Exp + 'a) -> Self {
        Focus(Rc::new(RefCell::new(Box::new(f))))
    }

    pub(crate) fn call(&self, istmts: &mut Vec<IntermediateStmt>) -> Exp {
        let res = self.0.replace(Box::new(|_| unreachable!()))(istmts);
        let res1 = res.clone();
        let _ = self.0.replace(Box::new(|_| res));
        res1
    }
}

type Constructor<'a> = Box<dyn FnOnce(&mut Vec<IntermediateStmt>, Exp) -> Exp + 'a>;

pub(crate) fn projections_to_expr<'tcx, 'a, N: Namer<'tcx>>(
    lower: &'a LoweringState<'_, 'tcx, N>,
    istmts: &mut Vec<IntermediateStmt>,
    mut place_ty: PlaceTy<'tcx>,
    // The term holding the currently 'focused' portion of the place
    mut focus: Focus<'a>,
    mut constructor: Constructor<'a>,
    proj: &'a [mir::ProjectionElem<Symbol, Ty<'tcx>>],
) -> (PlaceTy<'tcx>, Focus<'a>, Constructor<'a>) {
    for elem in proj {
        use rustc_middle::mir::ProjectionElem::*;
        // TODO: name hygiene
        match elem {
            Deref => {
                let mutable = place_ty.ty.is_mutable_ptr();
                if mutable {
                    let focus1 = focus.clone();
                    focus = Focus::new(move |is| focus.call(is).field("current".into()));
                    constructor = Box::new(move |is, t| {
                        let record = Box::new(focus1.call(is));
                        constructor(is, RecUp {
                            record,
                            updates: Box::new([("current".into(), t)]),
                        })
                    });
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) if def.is_enum() => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let fields: Box<[_]> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            Param::Term(
                                lower.fresh_from(format!("r{}", f.name)),
                                lower.ty(f.ty(lower.ctx.tcx, subst)),
                            )
                        })
                        .collect();

                    let acc_name = lower.names.eliminator(variant.def_id, subst);
                    let args = Box::new([Arg::Term(focus.call(istmts))]);
                    istmts.push(IntermediateStmt::Call(fields.clone(), acc_name, args));

                    let foc = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    focus = Focus::new(|_| foc);

                    constructor = Box::new(move |is, t| {
                        let constr = Exp::qvar(lower.names.constructor(variant.def_id, subst));
                        let mut fields: Box<[_]> =
                            fields.into_iter().map(|f| Exp::var(f.as_term().0.clone())).collect();
                        fields[ix.as_usize()] = t;
                        constructor(is, constr.app(fields))
                    });
                }
                TyKind::Adt(def, subst) => {
                    assert!(def.is_struct());

                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(lower.names.field(def.did(), subst, *ix))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates = Box::new([(lower.names.field(def.did(), subst, *ix), t)]);
                        if def.all_fields().count() == 1 {
                            constructor(is, Exp::Record { fields: updates })
                        } else {
                            let record = focus1.call(is).boxed();
                            constructor(is, Exp::RecUp { record, updates })
                        }
                    })
                }
                TyKind::Tuple(fields) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        let var = lower.fresh_from("r");
                        let mut pat: Box<[_]> = repeat_n(Wildcard, fields.len()).collect();
                        pat[ix.as_usize()] = VarP(var.clone());
                        Let {
                            pattern: TupleP(pat.clone()),
                            arg: focus.call(is).boxed(),
                            body: Exp::var(var).boxed(),
                        }
                    });

                    constructor = Box::new(move |is, t| {
                        let var_names: Vec<_> =
                            fields.iter().map(|_| lower.fresh_from("r")).collect();

                        let mut field_pats =
                            var_names.clone().into_iter().map(VarP).collect::<Box<[_]>>();
                        field_pats[ix.as_usize()] = Wildcard;

                        let mut varexps = var_names.into_iter().map(Exp::var).collect::<Box<[_]>>();
                        varexps[ix.as_usize()] = t;

                        let tuple = Let {
                            pattern: TupleP(field_pats),
                            arg: focus1.call(is).boxed(),
                            body: Exp::Tuple(varexps).boxed(),
                        };

                        constructor(is, tuple)
                    });
                }
                TyKind::Closure(id, subst) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(lower.names.field(*id, subst, *ix))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates = Box::new([(lower.names.field(*id, subst, *ix), t)]);

                        if subst.as_closure().upvar_tys().len() == 1 {
                            constructor(is, Exp::Record { fields: updates })
                        } else {
                            let record = focus1.call(is).boxed();
                            constructor(is, Exp::RecUp { record, updates })
                        }
                    });
                }
                _ => todo!("place: {:?}", place_ty.ty.kind()),
            },
            Index(ix) => {
                let elt_ty = projection_ty(place_ty, lower.ctx.tcx, *elem);
                let elt_ty = lower.ty(elt_ty.ty);
                let ty = lower.ty(place_ty.ty);
                // TODO: Use [_] syntax
                let ix_exp = Exp::var(Ident::build(ix.as_str()));

                let focus1 = focus.clone();
                let elt_ty1 = elt_ty.clone();
                let ix_exp1 = ix_exp.clone();
                focus = Focus::new(move |is| {
                    let result = lower.fresh_from("r");
                    let foc = focus.call(is);
                    is.push(IntermediateStmt::Call(
                        Box::new([Param::Term(result.clone(), elt_ty1.clone())]),
                        lower.names.in_pre(PreMod::Slice, "get"),
                        Box::new([Arg::Ty(elt_ty1), Arg::Term(foc), Arg::Term(ix_exp1)]),
                    ));

                    Exp::qvar(result.into())
                });

                constructor = Box::new(move |is, t| {
                    let out = lower.fresh_from("r");
                    let rhs = t;
                    let foc = focus1.call(is);

                    is.push(IntermediateStmt::Call(
                        Box::new([Param::Term(out.clone(), ty)]),
                        lower.names.in_pre(PreMod::Slice, "set"),
                        Box::new([
                            Arg::Ty(elt_ty),
                            Arg::Term(foc),
                            Arg::Term(ix_exp),
                            Arg::Term(rhs),
                        ]),
                    ));
                    constructor(is, Exp::qvar(out.into()))
                });
            }
            Downcast(_, _) => {}
            // UNSUPPORTED
            ConstantIndex { .. } => todo!(),
            Subslice { .. } => todo!(),
            OpaqueCast(_) => todo!(),
            Subtype(_) => todo!(),
        }
        place_ty = projection_ty(place_ty, lower.ctx.tcx, *elem);
    }

    (place_ty, focus, constructor)
}

pub(crate) fn rplace_to_expr<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    pl: &Place<'tcx>,
    istmts: &mut Vec<IntermediateStmt>,
) -> Exp {
    let place_ty = PlaceTy::from_ty(lower.locals[&pl.local].ty);
    let (_, rhs, _) = projections_to_expr(
        lower,
        istmts,
        place_ty,
        Focus::new(|_| Exp::var(ident_of(pl.local))),
        Box::new(|_, _| unreachable!()),
        &pl.projection,
    );
    rhs.call(istmts)
}

fn lplace_to_expr<'tcx, N: Namer<'tcx>>(
    lower: &LoweringState<'_, 'tcx, N>,
    pl: &Place<'tcx>,
    rhs: Exp,
    istmts: &mut Vec<IntermediateStmt>,
) -> Exp {
    let place_ty = PlaceTy::from_ty(lower.locals[&pl.local].ty);
    let (_, _, constructor) = projections_to_expr(
        lower,
        istmts,
        place_ty,
        Focus::new(|_| Exp::var(ident_of(pl.local))),
        Box::new(|_, x| x),
        &pl.projection,
    );

    constructor(istmts, rhs)
}

pub fn projection_ty<'tcx>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: ProjectionElem<Symbol, Ty<'tcx>>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, &elem, |_, _, ty| ty, |_, ty| ty)
}
