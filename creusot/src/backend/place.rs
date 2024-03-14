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
        Pattern::*,
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
    let inner = create_assign_rec(
        ctx,
        names,
        locals,
        PlaceTy::from_ty(locals[&lhs.local].ty),
        lhs.local,
        &lhs.projection,
        0,
        rhs.clone(),
    );

    let (rhs, mut stmts) = lplace_to_expr(ctx, names, locals, lhs.local, &lhs.projection, rhs);


    stmts.push(IntermediateStmt::Assign(Ident::build(lhs.local.as_str()), rhs));
    stmts
}

fn create_assign_rec<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    locals: &LocalDecls<'tcx>,
    place_ty: PlaceTy<'tcx>,
    base: Symbol,
    proj: &[ProjectionElem<Symbol, Ty<'tcx>>],
    proj_ix: usize,
    rhs: Exp,
) -> Exp {
    if proj_ix >= proj.len() {
        return rhs;
    }

    let inner = create_assign_rec(
        ctx,
        names,
        locals,
        projection_ty(place_ty, ctx.tcx, proj[proj_ix]),
        base,
        proj,
        proj_ix + 1,
        rhs,
    );
    let fvs = inner.fvs();
    let freshvars = (0..).map(|i| format!("x{i}").into()).filter(|x| !fvs.contains(x));
    use ProjectionElem::*;
    match &proj[proj_ix] {
        Deref => {
            use rustc_hir::Mutability::*;

            let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
            if mutability == Mut {
                RecUp {
                    record: Box::new(translate_rplace(ctx, names, locals, base, &proj[..proj_ix])),
                    updates: vec![("current".into(), inner)],
                }
            } else {
                inner
            }
        }
        Field(ix, _) => match place_ty.ty.kind() {
            TyKind::Adt(def, subst) => {
                let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                let variant = &def.variants()[variant_id];

                let varnames = freshvars.take(variant.fields.len()).collect::<Vec<Ident>>();
                let field_pats = varnames.clone().into_iter().map(|x| VarP(x)).collect();
                let mut varexps: Vec<Exp> = varnames.into_iter().map(|x| Exp::var(x)).collect();

                varexps[ix.as_usize()] = inner;

                let ctor = names.constructor(variant.def_id, subst);
                Let {
                    pattern: ConsP(ctor.clone(), field_pats),
                    arg: Box::new(translate_rplace(ctx, names, locals, base, &proj[..proj_ix])),
                    body: Box::new(Constructor { ctor, args: varexps }),
                }
            }
            TyKind::Tuple(fields) => {
                let varnames = freshvars.take(fields.len()).collect::<Vec<Ident>>();
                let field_pats = varnames.clone().into_iter().map(|x| VarP(x.into())).collect();
                let mut varexps: Vec<Exp> = varnames.into_iter().map(|x| Exp::var(x)).collect();

                varexps[ix.as_usize()] = inner;

                Let {
                    pattern: TupleP(field_pats),
                    arg: Box::new(translate_rplace(ctx, names, locals, base, &proj[..proj_ix])),
                    body: Box::new(Tuple(varexps)),
                }
            }
            TyKind::Closure(id, subst) => {
                let varnames =
                    freshvars.take(subst.as_closure().upvar_tys().len()).collect::<Vec<Ident>>();
                let field_pats = varnames.clone().into_iter().map(|x| VarP(x.into())).collect();
                let mut varexps: Vec<Exp> = varnames.into_iter().map(|x| Exp::var(x)).collect();

                varexps[ix.as_usize()] = inner;
                let cons = names.constructor(*id, subst);

                Let {
                    pattern: ConsP(cons.clone(), field_pats),
                    arg: Box::new(translate_rplace(ctx, names, locals, base, &proj[..proj_ix])),
                    body: Box::new(Exp::Constructor { ctor: cons, args: varexps }),
                }
            }
            _ => unreachable!(),
        },
        Downcast(_, _) => inner,
        Index(ix) => {
            let set = Exp::qvar(QName::from_string("Slice.set").unwrap());
            let ix_exp = Exp::var(Ident::build(ix.as_str()));

            Call(
                Box::new(set),
                vec![translate_rplace(ctx, names, locals, base, &proj[..proj_ix]), ix_exp, inner],
            )
        }
        ConstantIndex { .. } => unimplemented!("ConstantIndex"),
        Subslice { .. } => unimplemented!("Subslice"),
        OpaqueCast(_) => unimplemented!("OpaqueCast"),
        Subtype(_) => unimplemented!("Subtype"),
    }
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
    let mut constructor: Box<dyn FnOnce(coma::Term) -> coma::Term> = Box::new(|x| x);
    let mut istmts = Vec::new();

    for elem in proj {
        match elem {
            Deref => {
                use rustc_hir::Mutability::*;
                let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                if mutability == Mut {
                    let f = focus.clone();
                    constructor = Box::new(|t| {
                        constructor(RecUp {
                            record: Box::new(f),
                            updates: vec![("current".into(), t)],
                        })
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
                                format!("_{}", f.name).into(),
                                translate_ty(ctx, names, DUMMY_SP, f.ty(ctx.tcx, subst)),
                            )
                        })
                        .collect();

                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(
                        fields,
                        Expr::Symbol(acc_name),
                        vec![Arg::Term(focus)],
                    ));
                    let constr = Exp::qvar(names.constructor(variant.def_id, subst));
                    constructor = Box::new(|t| {
                        let mut fields: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|f| Exp::var(format!("_{}", f.name)))
                            .collect();
                        fields[ix.as_usize()] = t;
                        constructor(constr.app(fields))
                    });
                    focus = new_focus;
                }
                _ => todo!("{:?}", place_ty.ty.kind()),
            },
            Index(_) => todo!("Index"),
            Downcast(_, _) => {}
            // UNSUPPORTED
            ConstantIndex { offset, min_length, from_end } => todo!(),
            Subslice { from, to, from_end } => todo!(),
            OpaqueCast(_) => todo!(),
            Subtype(_) => todo!(),
        }
        place_ty = projection_ty(place_ty, ctx.tcx, *elem);
    }
    (constructor(rhs), istmts)
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
                                format!("_{}", f.name).into(),
                                translate_ty(ctx, names, DUMMY_SP, f.ty(ctx.tcx, subst)),
                            )
                        })
                        .collect();

                    let new_focus = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    istmts.push(IntermediateStmt::Call(
                        fields,
                        Expr::Symbol(acc_name),
                        vec![Arg::Term(focus)],
                    ));
                    focus = new_focus;
                }
                _ => todo!(),
            },
            Index(_) => todo!(),
            // Skip, always followed by a *field* where we do the real translation
            Downcast(_, _) => {}
            // Unusued
            Subslice { from, to, from_end } => unimplemented!("Subslice"),
            ConstantIndex { offset, min_length, from_end } => unimplemented!("ConstantIndex"),
            OpaqueCast(_) => unimplemented!("OpaqueCast"),
            Subtype(_) => unimplemented!("Subtype"),
        }

        place_ty = projection_ty(place_ty, ctx.tcx, *elem);
    }

    (focus, istmts)
}

// [(P as Some)]   ---> [_1]
// [(P as Some).0] ---> let Some(a) = [_1] in a
// [(* P)] ---> * [P]
pub(crate) fn translate_rplace<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    locals: &LocalDecls<'tcx>,
    loc: Symbol,
    proj: &[mir::ProjectionElem<Symbol, Ty<'tcx>>],
) -> Exp {
    let mut inner = Exp::var(Ident::build(loc.as_str()));
    if proj.is_empty() {
        return inner;
    }

    use rustc_middle::mir::ProjectionElem::*;
    let mut place_ty = PlaceTy::from_ty(locals[&loc].ty);

    for elem in proj {
        match elem {
            Deref => {
                use rustc_hir::Mutability::*;
                let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                if mutability == Mut {
                    inner = Current(Box::new(inner))
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let _variant = &def.variants()[variant_id];

                    ctx.translate_accessor(def.variants()[variant_id].fields[*ix].did);

                    let acc = names.accessor(def.did(), subst, variant_id.as_usize(), *ix);
                    inner = Call(Box::new(Exp::qvar(acc)), vec![inner]);
                }
                TyKind::Tuple(fields) => {
                    let mut pat = vec![Wildcard; fields.len()];
                    pat[ix.as_usize()] = VarP("a".into());

                    inner = Let {
                        pattern: TupleP(pat),
                        arg: Box::new(inner),
                        body: Box::new(Exp::var("a")),
                    }
                }
                TyKind::Closure(id, subst) => {
                    inner =
                        Call(Box::new(Exp::qvar(names.accessor(*id, subst, 0, *ix))), vec![inner]);
                }
                e => unreachable!("{:?}", e),
            },
            Downcast(_, _) => {}
            Index(ix) => {
                // TODO: Use [_] syntax
                let ix_exp = Exp::var(Ident::build(ix.as_str()));
                inner = Call(
                    Box::new(Exp::qvar(QName::from_string("Slice.get").unwrap())),
                    vec![inner, ix_exp],
                )
            }
            ConstantIndex { .. } => unimplemented!("constant index projection"),
            Subslice { .. } => unimplemented!("subslice projection"),
            OpaqueCast(_) => unimplemented!("opaque cast projection"),
            Subtype(_) => unimplemented!("Subtype"),
        }
        place_ty = projection_ty(place_ty, ctx.tcx, *elem);
    }

    inner
}

pub fn projection_ty<'tcx>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: ProjectionElem<Symbol, Ty<'tcx>>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, ty::ParamEnv::empty(), &elem, |_, _, ty| ty, |_, ty| ty)
}
