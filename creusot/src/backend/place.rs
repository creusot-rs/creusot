use crate::{
    ctx::CloneMap,
    translation::{
        fmir::{self, LocalDecls},
        projection_vec::map_projections,
    },
};
use rustc_middle::{
    mir::{self, tcx::PlaceTy, ProjectionElem},
    ty::{self, Ty, TyCtxt, TyKind},
};
use rustc_span::Symbol;
use std::fmt::Debug;
use why3::{
    exp::{
        Exp::{self, *},
        Pattern::*,
        Purity,
    },
    mlcfg::{
        Statement::*,
        {self},
    },
    Ident, QName,
};

use super::Why3Generator;

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
) -> mlcfg::Statement {
    let inner = create_assign_rec(
        ctx,
        names,
        locals,
        PlaceTy::from_ty(locals[&lhs.local].ty),
        lhs.local,
        &lhs.projection,
        0,
        rhs,
    );

    Assign { lhs: Ident::build(lhs.local.as_str()), rhs: inner }
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
        projection_ty(place_ty, ctx.tcx, &proj[proj_ix]),
        base,
        proj,
        proj_ix + 1,
        rhs,
    );
    use ProjectionElem::*;
    match &proj[proj_ix] {
        Deref => {
            use rustc_hir::Mutability::*;

            let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
            if mutability == Mut {
                RecUp {
                    record: Box::new(translate_rplace(ctx, names, locals, base, &proj[..proj_ix])),
                    updates: vec![
                        ("current".into(), inner),
                        (
                            "addr".into(),
                            Exp::Call(
                                Box::new(Exp::QVar(
                                    QName {
                                        module: vec!["Borrow".into()],
                                        name: "make_new_addr".into(),
                                    },
                                    why3::exp::Purity::Logic,
                                )),
                                vec![Exp::Tuple(Vec::new())],
                            ),
                        ),
                    ],
                }
            } else {
                inner
            }
        }
        Field(ix, _) => match place_ty.ty.kind() {
            TyKind::Adt(def, subst) => {
                let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                let variant = &def.variants()[variant_id];
                let var_size = variant.fields.len();

                let field_pats =
                    ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                let mut varexps: Vec<Exp> =
                    ('a'..).map(|c| Exp::impure_var(c.to_string().into())).take(var_size).collect();

                varexps[ix.as_usize()] = inner;

                let ctor = names.constructor(variant.def_id, subst);
                Let {
                    pattern: ConsP(ctor.clone(), field_pats),
                    arg: Box::new(translate_rplace(ctx, names, locals, base, &proj[..proj_ix])),
                    body: Box::new(Constructor { ctor, args: varexps }),
                }
            }
            TyKind::Tuple(fields) => {
                let var_size = fields.len();

                let field_pats =
                    ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                let mut varexps: Vec<Exp> =
                    ('a'..).map(|c| Exp::impure_var(c.to_string().into())).take(var_size).collect();

                varexps[ix.as_usize()] = inner;

                Let {
                    pattern: TupleP(field_pats),
                    arg: Box::new(translate_rplace(ctx, names, locals, base, &proj[..proj_ix])),
                    body: Box::new(Tuple(varexps)),
                }
            }
            TyKind::Closure(id, subst) => {
                let count = subst.as_closure().upvar_tys().count();
                let field_pats = ('a'..).map(|c| VarP(c.to_string().into())).take(count).collect();

                let mut varexps: Vec<Exp> =
                    ('a'..).map(|c| Exp::impure_var(c.to_string().into())).take(count).collect();

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
            let set = Exp::impure_qvar(QName::from_string("Slice.set").unwrap());
            let ix_exp = Exp::impure_var(Ident::build(ix.as_str()));

            Call(
                Box::new(set),
                vec![translate_rplace(ctx, names, locals, base, &proj[..proj_ix]), ix_exp, inner],
            )
        }
        ConstantIndex { .. } => unimplemented!("ConstantIndex"),
        Subslice { .. } => unimplemented!("Subslice"),
        OpaqueCast(_) => unimplemented!("OpaqueCast"),
    }
}

pub(crate) fn translate_rplace<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    locals: &LocalDecls<'tcx>,
    loc: Symbol,
    proj: &[mir::ProjectionElem<Symbol, Ty<'tcx>>],
) -> Exp {
    let proj =
        map_projections(proj.iter().copied(), |loc| Exp::impure_var(Ident::build(loc.as_str())));
    let inner = Exp::impure_var(Ident::build(loc.as_str()));
    translate_rplace_gen(ctx, names, inner, locals[&loc].ty, proj, Purity::Program)
}

// [(P as Some)]   ---> [_1]
// [(P as Some).0] ---> let Some(a) = [_1] in a
// [(* P)] ---> * [P]
pub(crate) fn translate_rplace_gen<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    mut inner: Exp,
    ty: Ty<'tcx>,
    proj: impl Iterator<Item = ProjectionElem<Exp, Ty<'tcx>>>,
    purity: Purity,
) -> Exp {
    use rustc_middle::mir::ProjectionElem::*;
    let mut place_ty = PlaceTy::from_ty(ty);

    for elem in proj {
        let next_place_ty = projection_ty(place_ty, ctx.tcx, &elem);
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

                    ctx.translate_accessor(def.variants()[variant_id].fields[ix].did);

                    let acc = names.accessor(def.did(), subst, variant_id.as_usize(), ix);
                    inner = Call(Box::new(QVar(acc, purity)), vec![inner]);
                }
                TyKind::Tuple(fields) => {
                    let mut pat = vec![Wildcard; fields.len()];
                    pat[ix.as_usize()] = VarP("a".into());

                    inner = Let {
                        pattern: TupleP(pat),
                        arg: Box::new(inner),
                        body: Box::new(Var("a".into(), purity)),
                    }
                }
                TyKind::Closure(id, subst) => {
                    inner = Call(
                        Box::new(QVar(names.accessor(*id, subst, 0, ix), purity)),
                        vec![inner],
                    );
                }
                e => unreachable!("{:?}", e),
            },
            Downcast(_, _) => {}
            Index(ix) => {
                inner = Call(
                    Box::new(QVar(QName::from_string("Slice.get").unwrap(), purity)),
                    vec![inner, ix],
                )
            }
            ConstantIndex { .. } => unimplemented!("constant index projection"),
            Subslice { .. } => unimplemented!("subslice projection"),
            OpaqueCast(_) => unimplemented!("opaque cast projection"),
        }
        place_ty = next_place_ty;
    }

    inner
}

pub fn projection_ty<'tcx, V: Debug>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: &ProjectionElem<V, Ty<'tcx>>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, ty::ParamEnv::empty(), elem, |_, _, ty| ty, |_, ty| ty)
}
