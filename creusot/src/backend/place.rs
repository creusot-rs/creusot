use crate::{
    backend::Namer,
    ctx::PreMod,
    fmir::{Place, ProjectionElem},
    naming::name,
};
use rustc_middle::{
    mir::tcx::PlaceTy,
    ty::{TyCtxt, TyKind},
};
use std::{cell::RefCell, rc::Rc};
use why3::{
    Ident, Name,
    coma::{Arg, Param},
    exp::Exp,
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
    istmts.push(IntermediateStmt::Assign(lhs.local, rhs));
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
    proj: &'a [ProjectionElem<'tcx>],
) -> (PlaceTy<'tcx>, Focus<'a>, Constructor<'a>) {
    for elem in proj {
        use rustc_middle::mir::ProjectionElem::*;
        // TODO: name hygiene
        match elem {
            Deref => {
                let mutable = place_ty.ty.is_mutable_ptr();
                if mutable {
                    let focus1 = focus.clone();
                    focus =
                        Focus::new(move |is| focus.call(is).field(Name::Global(name::current())));
                    constructor = Box::new(move |is, t| {
                        let record = Box::new(focus1.call(is));
                        constructor(is, Exp::RecUp {
                            record,
                            updates: Box::new([(Name::Global(name::current()), t)]),
                        })
                    });
                }
            }
            &Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) if def.is_enum() => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let fields: Box<[_]> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            Param::Term(
                                Ident::fresh_local(&format!("r{}", f.name)),
                                lower.ty(f.ty(lower.ctx.tcx, subst)),
                            )
                        })
                        .collect();

                    let acc_name = lower.names.eliminator(variant.def_id, subst);
                    let args = Box::new([Arg::Term(focus.call(istmts))]);
                    istmts.push(IntermediateStmt::Call(
                        fields.clone(),
                        Name::local(acc_name),
                        args,
                    ));

                    let foc = Exp::var(fields[ix.as_usize()].as_term().0);
                    focus = Focus::new(|_| foc);

                    constructor = Box::new(move |is, t| {
                        let constr = Exp::var(lower.names.constructor(variant.def_id, subst));
                        let mut fields: Box<[_]> =
                            fields.into_iter().map(|f| Exp::var(f.as_term().0)).collect();
                        fields[ix.as_usize()] = t;
                        constructor(is, constr.app(fields))
                    });
                }
                TyKind::Adt(def, subst) => {
                    assert!(def.is_struct());

                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(Name::local(lower.names.field(def.did(), subst, ix)))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates =
                            Box::new([(Name::local(lower.names.field(def.did(), subst, ix)), t)]);
                        if def.all_fields().count() == 1 {
                            constructor(is, Exp::Record { fields: updates })
                        } else {
                            let record = focus1.call(is).boxed();
                            constructor(is, Exp::RecUp { record, updates })
                        }
                    })
                }
                TyKind::Tuple(args) if args.len() == 1 => {}
                TyKind::Tuple(args) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(Name::local(lower.names.tuple_field(args, ix)))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates =
                            Box::new([(Name::local(lower.names.tuple_field(args, ix)), t)]);
                        let record = focus1.call(is).boxed();
                        constructor(is, Exp::RecUp { record, updates })
                    });
                }
                TyKind::Closure(id, subst) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(Name::local(lower.names.field(*id, subst, ix)))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates =
                            Box::new([(Name::local(lower.names.field(*id, subst, ix)), t)]);
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
                let ix_exp = Exp::var(*ix);

                let focus1 = focus.clone();
                let elt_ty1 = elt_ty.clone();
                let ix_exp1 = ix_exp.clone();
                focus = Focus::new(move |is| {
                    let result = Ident::fresh_local("r");
                    let foc = focus.call(is);
                    is.push(IntermediateStmt::Call(
                        Box::new([Param::Term(result.clone(), elt_ty1.clone())]),
                        Name::Global(lower.names.in_pre(PreMod::Slice, "get")),
                        Box::new([Arg::Ty(elt_ty1), Arg::Term(foc), Arg::Term(ix_exp1)]),
                    ));
                    Exp::var(result)
                });

                constructor = Box::new(move |is, t| {
                    let out = Ident::fresh_local("r");
                    let rhs = t;
                    let foc = focus1.call(is);

                    is.push(IntermediateStmt::Call(
                        Box::new([Param::Term(out.clone(), ty)]),
                        Name::Global(lower.names.in_pre(PreMod::Slice, "set")),
                        Box::new([
                            Arg::Ty(elt_ty),
                            Arg::Term(foc),
                            Arg::Term(ix_exp),
                            Arg::Term(rhs),
                        ]),
                    ));
                    constructor(is, Exp::var(out))
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
        Focus::new(|_| Exp::var(pl.local)),
        Box::new(|_, _| unreachable!()),
        &pl.projections,
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
        Focus::new(|_| Exp::var(pl.local)),
        Box::new(|_, x| x),
        &pl.projections,
    );

    constructor(istmts, rhs)
}

pub fn projection_ty<'tcx>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: ProjectionElem<'tcx>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, &elem, |_, _, ty| ty, |_, ty| ty)
}
