use crate::{backend::Namer, fmir::Place, util};
use rustc_middle::{
    mir::{self, tcx::PlaceTy, ProjectionElem},
    ty::{self, Ty, TyCtxt, TyKind},
};
use rustc_span::Symbol;
use rustc_type_ir::AliasTyKind;
use why3::{
    coma::{self, Arg, Expr, Param},
    exp::{
        Exp::{self, *},
        Pattern::*,
    },
    Ident, QName,
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
    lower: &mut LoweringState<'_, 'tcx, N>,
    lhs: &Place<'tcx>,
    rhs: Exp,
    istmts: &mut Vec<IntermediateStmt>,
) {
    let rhs = lplace_to_expr(lower, lhs.local, &lhs.projection, rhs, istmts);
    istmts.push(IntermediateStmt::Assign(Ident::build(lhs.local.as_str()), rhs));
}

fn lplace_to_expr<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    loc: Symbol,
    proj: &[mir::ProjectionElem<Symbol, Ty<'tcx>>],
    rhs: coma::Term,
    istmts: &mut Vec<IntermediateStmt>,
) -> Exp {
    let mut focus = Exp::var(util::ident_of(loc));
    use rustc_middle::mir::ProjectionElem::*;
    let mut place_ty = PlaceTy::from_ty(lower.locals[&loc].ty);
    let mut constructor: Box<dyn FnOnce(&mut Vec<IntermediateStmt>, coma::Term) -> coma::Term> =
        Box::new(|_, x| x);

    let fresh_vars = |lower: &mut LoweringState<'_, 'tcx, _>, n| -> Vec<_> {
        (0..n).map(|_| lower.fresh_from("l")).collect()
    };

    for elem in proj {
        match elem {
            Deref => {
                let mutable = place_ty.ty.is_mutable_ptr();
                if mutable {
                    let f = focus.clone();
                    constructor = Box::new(|is, t| {
                        constructor(
                            is,
                            RecUp { record: Box::new(f), updates: vec![("current".into(), t)] },
                        )
                    });
                    focus = focus.field("current")
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let acc_name = lower.names.eliminator(variant.def_id, subst);
                    let fields: Vec<_> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            Param::Term(
                                lower.fresh_from(format!("l_{}", f.name)),
                                lower.ty(f.ty(lower.ctx.tcx, subst)),
                            )
                        })
                        .collect();
                    let projections = lower.ctx.projections_in_ty(def.did()).to_vec();

                    let mut ty_projections = Vec::new();
                    for p in projections {
                        let n = lower.names.normalize(&lower.ctx, p);
                        let ty = lower.ty(lower
                            .ctx
                            .mk_ty_from_kind(TyKind::Alias(AliasTyKind::Projection, n)));
                        ty_projections.push(ty);
                    }

                    let params = subst
                        .iter()
                        .flat_map(|ty| ty.as_type())
                        .map(|ty| lower.ty(ty))
                        .chain(ty_projections)
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus)))
                        .collect();

                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(
                        fields.clone(),
                        Expr::Symbol(acc_name),
                        params,
                    ));
                    let constr = Exp::qvar(lower.names.constructor(variant.def_id, subst));
                    constructor = Box::new(|is, t| {
                        let mut fields: Vec<_> =
                            fields.into_iter().map(|f| Exp::var(f.as_term().0.clone())).collect();
                        fields[ix.as_usize()] = t;
                        // TODO: Only emit type if the constructor would otherwise be ambiguous
                        constructor(is, constr.app(fields))
                    });
                    focus = new_focus;
                }
                TyKind::Tuple(fields) => {
                    let ix_name = lower.fresh_from("l");
                    let mut field_pats: Vec<_> = (0..fields.len()).map(|_| Wildcard).collect();
                    field_pats[ix.as_usize()] = VarP(ix_name.clone());
                    let old_focus = focus.clone();
                    focus = Let {
                        pattern: TupleP(field_pats.clone()),
                        arg: Box::new(focus),
                        body: Box::new(Exp::var(ix_name)),
                    };

                    let var_names = fresh_vars(lower, fields.len());
                    let mut field_pats =
                        var_names.clone().into_iter().map(VarP).collect::<Vec<_>>();
                    field_pats[ix.as_usize()] = Wildcard;

                    let mut varexps = var_names.into_iter().map(Exp::var).collect::<Vec<_>>();
                    constructor = Box::new(|is, t| {
                        varexps[ix.as_usize()] = t;
                        let tuple = Let {
                            pattern: TupleP(field_pats),
                            arg: Box::new(old_focus),
                            body: Box::new(Exp::Tuple(varexps)),
                        };

                        constructor(is, tuple)
                    });
                }
                TyKind::Closure(id, subst) => {
                    let acc_name = lower.names.eliminator(*id, subst);
                    let upvars = subst.as_closure().upvar_tys();
                    let upvar_cnt = upvars.len();
                    let field_names = fresh_vars(lower, upvar_cnt);
                    let fields: Vec<_> = field_names
                        .iter()
                        .cloned()
                        .zip(upvars)
                        .map(|(id, ty)| Param::Term(id, lower.ty(ty)))
                        .collect();
                    let params = subst
                        .as_closure()
                        .parent_args()
                        .iter()
                        .flat_map(|arg| arg.as_type())
                        .map(|ty| lower.ty(ty))
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus)))
                        .collect();
                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(fields, Expr::Symbol(acc_name), params));

                    let constr = Exp::qvar(lower.names.constructor(*id, subst));
                    constructor = Box::new(|is, t| {
                        let mut fields: Vec<_> =
                            field_names.into_iter().map(|f| Exp::var(f)).collect();
                        fields[ix.as_usize()] = t;
                        // TODO: Only emit type if the constructor would otherwise be ambiguous
                        constructor(is, constr.app(fields))
                    });
                    focus = new_focus;
                }
                _ => todo!("place: {:?}", place_ty.ty.kind()),
            },
            Index(ix) => {
                let elt_ty = projection_ty(place_ty, lower.ctx.tcx, *elem);

                let elt_ty = lower.ty(elt_ty.ty);
                let ty = lower.ty(place_ty.ty);
                // TODO: Use [_] syntax
                let ix_exp = Exp::var(Ident::build(ix.as_str()));
                let result = lower.fresh_from("l");
                istmts.push(IntermediateStmt::Call(
                    vec![Param::Term(result.clone(), elt_ty.clone())],
                    Expr::Symbol(QName::from_string("Slice.get").unwrap()),
                    vec![
                        Arg::Ty(elt_ty.clone()),
                        Arg::Term(focus.clone()),
                        Arg::Term(ix_exp.clone()),
                    ],
                ));

                let old_focus = focus;
                focus = Exp::qvar(result.into());
                let set = QName::from_string("Slice.set").unwrap();

                let out = lower.fresh_from("l");
                constructor = Box::new(|is, t| {
                    let rhs = t;

                    is.push(IntermediateStmt::Call(
                        vec![Param::Term(out.clone(), ty)],
                        Expr::Symbol(set),
                        vec![
                            Arg::Ty(elt_ty),
                            Arg::Term(old_focus),
                            Arg::Term(ix_exp),
                            Arg::Term(rhs),
                        ],
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
    let term = constructor(istmts, rhs);
    term
}

pub(crate) fn projections_to_expr<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    // The term holding the currently 'focused' portion of the place
    (mut focus, mut place_ty): (Exp, PlaceTy<'tcx>),
    proj: &[mir::ProjectionElem<Symbol, Ty<'tcx>>],
    istmts: &mut Vec<IntermediateStmt>,
) -> (Exp, PlaceTy<'tcx>) {
    // TODO: name hygiene
    for elem in proj {
        use rustc_middle::mir::ProjectionElem::*;
        match elem {
            Deref => {
                let mutable = place_ty.ty.is_mutable_ptr();
                if mutable {
                    focus = focus.field("current")
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let acc_name = lower.names.eliminator(variant.def_id, subst);
                    let fields: Vec<_> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            Param::Term(
                                lower.fresh_from(format!("r{}", f.name)),
                                lower.ty(f.ty(lower.ctx.tcx, subst)),
                            )
                        })
                        .collect();

                    let projections = lower.ctx.projections_in_ty(def.did()).to_vec();

                    let mut ty_projections = Vec::new();
                    for p in projections {
                        let n = lower.names.normalize(&lower.ctx, p);
                        let ty = lower.ty(lower
                            .ctx
                            .mk_ty_from_kind(TyKind::Alias(AliasTyKind::Projection, n)));
                        ty_projections.push(ty);
                    }

                    let params = subst
                        .iter()
                        .flat_map(|ty| ty.as_type())
                        .map(|ty| lower.ty(ty))
                        .chain(ty_projections)
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus)))
                        .collect();

                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(fields, Expr::Symbol(acc_name), params));
                    focus = new_focus;
                }
                TyKind::Tuple(fields) => {
                    let var = lower.fresh_from("r");
                    let mut pat = vec![Wildcard; fields.len()];
                    pat[ix.as_usize()] = VarP(var.clone());

                    focus = Let {
                        pattern: TupleP(pat),
                        arg: Box::new(focus),
                        body: Box::new(Exp::var(var)),
                    }
                }
                TyKind::Closure(id, subst) => {
                    let acc_name = lower.names.eliminator(*id, subst);
                    let upvars = subst.as_closure().upvar_tys();

                    let fields: Vec<_> = upvars
                        .into_iter()
                        .map(|ty| Param::Term(lower.fresh_from("r"), lower.ty(ty)))
                        .collect();

                    let params = subst
                        .as_closure()
                        .parent_args()
                        .iter()
                        .flat_map(|arg| arg.as_type())
                        .map(|ty| lower.ty(ty))
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus)))
                        .collect();
                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(fields, Expr::Symbol(acc_name), params));
                    focus = new_focus;
                }
                _ => todo!(),
            },
            Index(ix) => {
                let elt_ty = projection_ty(place_ty, lower.ctx.tcx, *elem);
                let elt_ty = lower.ty(elt_ty.ty);
                // TODO: Use [_] syntax
                let ix_exp = Exp::var(Ident::build(ix.as_str()));
                let res = lower.fresh_from("r");
                istmts.push(IntermediateStmt::Call(
                    vec![Param::Term(res.clone(), elt_ty.clone())],
                    Expr::Symbol(QName::from_string("Slice.get").unwrap()),
                    vec![Arg::Ty(elt_ty.clone()), Arg::Term(focus), Arg::Term(ix_exp)],
                ));
                focus = Exp::qvar(res.into());
            }
            // Skip, always followed by a *field* where we do the real translation
            Downcast(_, _) => {}
            // Unused
            Subslice { .. } => unimplemented!("Subslice"),
            ConstantIndex { .. } => unimplemented!("ConstantIndex"),
            OpaqueCast(_) => unimplemented!("OpaqueCast"),
            Subtype(_) => unimplemented!("Subtype"),
        }

        place_ty = projection_ty(place_ty, lower.ctx.tcx, *elem);
    }

    (focus, place_ty)
}

pub(crate) fn rplace_to_expr<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    pl: &Place<'tcx>,
    istmts: &mut Vec<IntermediateStmt>,
) -> Exp {
    let focus = Exp::var(util::ident_of(pl.local));
    let place_ty = PlaceTy::from_ty(lower.locals[&pl.local].ty);

    projections_to_expr(lower, (focus, place_ty), &pl.projection, istmts).0
}

pub fn projection_ty<'tcx>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: ProjectionElem<Symbol, Ty<'tcx>>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, ty::ParamEnv::empty(), &elem, |_, _, ty| ty, |_, ty| ty)
}
