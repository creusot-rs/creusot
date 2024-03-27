use crate::{
    backend::{ty::translate_ty, Namer},
    ctx::CloneMap,
    translation::fmir::{self, LocalDecls},
    util,
};
use rustc_middle::{
    mir::{self, tcx::PlaceTy, ProjectionElem},
    ty::{self, Ty, TyCtxt, TyKind},
};
use rustc_span::{Span, Symbol, DUMMY_SP};
use why3::{
    coma::{self, Arg, Expr, Param},
    exp::{
        Exp::{self, *},
        Pattern::{self, *},
    },
    Ident, QName,
};

use super::{program::IntermediateStmt, Why3Generator};

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
pub(crate) fn create_assign_inner<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    locals: &LocalDecls<'tcx>,
    lhs: &fmir::Place<'tcx>,
    rhs: Exp,
    _: Span,
) -> Vec<IntermediateStmt> {
    let (rhs, mut stmts) = lplace_to_expr(ctx, names, locals, lhs.local, &lhs.projection, rhs);

    stmts.push(IntermediateStmt::Assign(Ident::build(lhs.local.as_str()), rhs));
    stmts
}

pub(crate) fn lplace_to_expr<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    locals: &LocalDecls<'tcx>,
    loc: Symbol,
    proj: &[mir::ProjectionElem<Symbol, Ty<'tcx>>],
    rhs: coma::Term,
) -> (Exp, Vec<IntermediateStmt>) {
    let mut focus = Exp::var(util::ident_of(loc));
    use rustc_middle::mir::ProjectionElem::*;
    let mut place_ty = PlaceTy::from_ty(locals[&loc].ty);
    let mut constructor: Box<dyn FnOnce(&mut Vec<IntermediateStmt>, coma::Term) -> coma::Term> =
        Box::new(|_, x| x);
    let mut istmts = Vec::new();

    let freshvars = &mut (0..).map(|i| -> Ident { format!("r{i}'").into() });

    for elem in proj {
        match elem {
            Deref => {
                use rustc_hir::Mutability::*;
                let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                if mutability == Mut {
                    let f = focus.clone();
                    constructor = Box::new(|is, t| {
                        constructor(
                            is,
                            RecUp { record: Box::new(f), updates: vec![("current".into(), t)] },
                        )
                    });
                    focus = Exp::Current(Box::new(focus))
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let acc_name = names.eliminator(variant.def_id, subst);
                    let fields: Vec<_> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            Param::Term(
                                format!("f_{}'", f.name).into(),
                                translate_ty(ctx, names, DUMMY_SP, f.ty(ctx.tcx, subst)),
                            )
                        })
                        .collect();
                    let params = subst
                        .iter()
                        .flat_map(|ty| ty.as_type())
                        .map(|ty| translate_ty(ctx, names, DUMMY_SP, ty))
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus)))
                        .collect();

                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(fields, Expr::Symbol(acc_name), params));
                    let constr = Exp::qvar(names.constructor(variant.def_id, subst));
                    constructor = Box::new(|is, t| {
                        let mut fields: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|f| Exp::var(format!("f_{}'", f.name)))
                            .collect();
                        fields[ix.as_usize()] = t;
                        constructor(is, constr.app(fields))
                    });
                    focus = new_focus;
                }
                // TODO(xavier): refactor to use a local let binding instead of recalculating hte tuple path each time
                TyKind::Tuple(fields) => {
                    let ix_name = freshvars.next().map(Ident::from).unwrap();
                    let mut field_pats: Vec<_> = (0..fields.len()).map(|_| Wildcard).collect();
                    field_pats[ix.as_usize()] = VarP(ix_name.clone());
                    let old_focus = focus.clone();
                    focus = Let {
                        pattern: TupleP(field_pats.clone()),
                        arg: Box::new(focus),
                        body: Box::new(Exp::var(ix_name)),
                    };

                    let var_names = freshvars.take(fields.len()).collect::<Vec<Ident>>();
                    let mut field_pats = var_names.clone().into_iter().map(VarP).collect::<Vec<_>>();
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
                _ => todo!("place: {:?}", place_ty.ty.kind()),
            },
            Index(ix) => {
                let elt_ty = projection_ty(place_ty, ctx.tcx, *elem);

                let elt_ty = translate_ty(ctx, names, DUMMY_SP, elt_ty.ty);
                let ty = translate_ty(ctx, names, DUMMY_SP, place_ty.ty);
                // TODO: Use [_] syntax
                let ix_exp = Exp::var(Ident::build(ix.as_str()));
                let result = freshvars.next().unwrap();
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

                let out = freshvars.next().unwrap();
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
        place_ty = projection_ty(place_ty, ctx.tcx, *elem);
    }
    let mut rhs_stmts = Vec::new();
    let term = constructor(&mut rhs_stmts, rhs);
    // rhs_stmts.reverse();
    istmts.extend(rhs_stmts.into_iter());
    (term, istmts)
}

pub(crate) fn rplace_to_expr<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    locals: &LocalDecls<'tcx>,
    loc: Symbol,
    proj: &[mir::ProjectionElem<Symbol, Ty<'tcx>>],
) -> (Exp, Vec<IntermediateStmt>) {
    let mut istmts = Vec::new();

    // The term holding the currently 'focused' portion of the place
    let mut focus = Exp::var(util::ident_of(loc));
    use rustc_middle::mir::ProjectionElem::*;
    let mut place_ty = PlaceTy::from_ty(locals[&loc].ty);

    let freshvars = &mut (0..).map(|i| -> Ident { format!("l{i}'").into() });

    // TODO: name hygiene
    for elem in proj {
        match elem {
            Deref => {
                use rustc_hir::Mutability::*;
                let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                if mutability == Mut {
                    focus = Exp::Current(Box::new(focus))
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let acc_name = names.eliminator(variant.def_id, subst);
                    let fields: Vec<_> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            Param::Term(
                                format!("f_{}'", f.name).into(),
                                translate_ty(ctx, names, DUMMY_SP, f.ty(ctx.tcx, subst)),
                            )
                        })
                        .collect();

                    let params = subst
                        .iter()
                        .flat_map(|ty| ty.as_type())
                        .map(|ty| translate_ty(ctx, names, DUMMY_SP, ty))
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus)))
                        .collect();

                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(fields, Expr::Symbol(acc_name), params));
                    focus = new_focus;
                }
                TyKind::Tuple(fields) => {
                    let var = freshvars.next().unwrap();
                    let mut pat = vec![Wildcard; fields.len()];
                    pat[ix.as_usize()] = VarP(var.clone());

                    focus = Let {
                        pattern: TupleP(pat),
                        arg: Box::new(focus),
                        body: Box::new(Exp::var(var)),
                    }
                }
                TyKind::Closure(_, _) => todo!("closure"),
                _ => todo!(),
            },
            Index(ix) => {
                let elt_ty = projection_ty(place_ty, ctx.tcx, *elem);
                let elt_ty = translate_ty(ctx, names, DUMMY_SP, elt_ty.ty);
                // TODO: Use [_] syntax
                let ix_exp = Exp::var(Ident::build(ix.as_str()));
                let res = freshvars.next().unwrap();
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

        place_ty = projection_ty(place_ty, ctx.tcx, *elem);
    }

    (focus, istmts)
}

pub fn projection_ty<'tcx>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: ProjectionElem<Symbol, Ty<'tcx>>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, ty::ParamEnv::empty(), &elem, |_, _, ty| ty, |_, ty| ty)
}
