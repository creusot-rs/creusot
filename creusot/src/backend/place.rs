use crate::{
    ctx::{BodyId, CloneMap, TranslationCtx},
    translation::LocalIdent,
};
use rustc_middle::{
    mir::{tcx::PlaceTy, HasLocalDecls, Local, Place, PlaceRef},
    ty::TyKind,
};
use why3::{
    exp::{
        Exp::{self, *},
        Pattern::*,
    },
    mlcfg::{
        Statement::*,
        {self},
    },
    QName,
};

use super::Why3Generator;

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn place_ty(&mut self, body_id: BodyId, pl: PlaceRef<'tcx>) -> PlaceTy<'tcx> {
        let local_ty = self.body(body_id).local_decls()[pl.local].ty;
        pl.projection.iter().fold(PlaceTy::from_ty(local_ty), |place_ty, &elem| {
            place_ty.projection_ty(self.tcx, elem)
        })
    }
}

impl<'tcx> TranslationCtx<'tcx> {
    pub(crate) fn translate_local(&mut self, body_id: BodyId, loc: Local) -> LocalIdent {
        let body = self.body(body_id);

        use rustc_middle::mir::VarDebugInfoContents::Place;
        let debug_info: Vec<_> = body
            .var_debug_info
            .iter()
            .filter(|var_info| match var_info.value {
                Place(p) => p.as_local().map(|l| l == loc).unwrap_or(false),
                _ => false,
            })
            .collect();

        assert!(debug_info.len() <= 1, "expected at most one debug entry for local {:?}", loc);
        match debug_info.get(0) {
            Some(info) => LocalIdent::dbg(loc, *info),
            None => LocalIdent::anon(loc),
        }
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
pub(crate) fn create_assign_inner<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    body_id: BodyId,
    lhs: &Place<'tcx>,
    rhs: Exp,
) -> mlcfg::Statement {
    // Translation happens inside to outside, which means we scan projection elements in reverse
    // building up the inner expression. We start with the RHS expression which is at the deepest
    // level.

    let mut inner = rhs;

    // Each level of the translation needs access to the _previous_ value at this nesting level
    // So we track the path from the root as we traverse, which we call the stump.
    let mut stump: &[_] = lhs.projection;

    use rustc_middle::mir::ProjectionElem::*;

    for (proj, elem) in lhs.iter_projections().rev() {
        // twisted stuff
        stump = &stump[0..stump.len() - 1];
        let place_ty = ctx.place_ty(body_id, proj);

        match elem {
            Deref => {
                use rustc_hir::Mutability::*;

                let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                if mutability == Mut {
                    inner = RecUp {
                        record: Box::new(translate_rplace_inner(
                            ctx, names, body_id, lhs.local, stump,
                        )),
                        label: "current".into(),
                        val: Box::new(inner),
                    }
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let var_size = variant.fields.len();

                    let field_pats =
                        ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                    let mut varexps: Vec<Exp> = ('a'..)
                        .map(|c| Exp::impure_var(c.to_string().into()))
                        .take(var_size)
                        .collect();

                    varexps[ix.as_usize()] = inner;

                    let ctor = names.constructor(variant.def_id, subst);
                    inner = Let {
                        pattern: ConsP(ctor.clone(), field_pats),
                        arg: Box::new(translate_rplace_inner(
                            ctx, names, body_id, lhs.local, stump,
                        )),
                        body: Box::new(Constructor { ctor, args: varexps }),
                    }
                }
                TyKind::Tuple(fields) => {
                    let var_size = fields.len();

                    let field_pats =
                        ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                    let mut varexps: Vec<Exp> = ('a'..)
                        .map(|c| Exp::impure_var(c.to_string().into()))
                        .take(var_size)
                        .collect();

                    varexps[ix.as_usize()] = inner;

                    inner = Let {
                        pattern: TupleP(field_pats),
                        arg: Box::new(translate_rplace_inner(
                            ctx, names, body_id, lhs.local, stump,
                        )),
                        body: Box::new(Tuple(varexps)),
                    }
                }
                TyKind::Closure(id, subst) => {
                    let count = subst.as_closure().upvar_tys().count();
                    let field_pats =
                        ('a'..).map(|c| VarP(c.to_string().into())).take(count).collect();

                    let mut varexps: Vec<Exp> = ('a'..)
                        .map(|c| Exp::impure_var(c.to_string().into()))
                        .take(count)
                        .collect();

                    varexps[ix.as_usize()] = inner;
                    let cons = names.constructor(*id, subst);

                    inner = Let {
                        pattern: ConsP(cons.clone(), field_pats),
                        arg: Box::new(translate_rplace_inner(
                            ctx, names, body_id, lhs.local, stump,
                        )),
                        body: Box::new(Exp::Constructor { ctor: cons, args: varexps }),
                    }
                }
                _ => unreachable!(),
            },
            Downcast(_, _) => {}
            Index(ix) => {
                let set = Exp::impure_qvar(QName::from_string("Slice.set").unwrap());
                let ix_exp = Exp::impure_var(ctx.translate_local(body_id, ix).ident());

                inner = Call(
                    Box::new(set),
                    vec![
                        translate_rplace_inner(ctx, names, body_id, lhs.local, stump),
                        ix_exp,
                        inner,
                    ],
                )
            }
            ConstantIndex { .. } => unimplemented!("ConstantIndex"),
            Subslice { .. } => unimplemented!("Subslice"),
            OpaqueCast(_) => unimplemented!("OpaqueCast"),
        }
    }

    let ident = ctx.translate_local(body_id, lhs.local);
    Assign { lhs: ident.ident(), rhs: inner }
}

// [(P as Some)]   ---> [_1]
// [(P as Some).0] ---> let Some(a) = [_1] in a
// [(* P)] ---> * [P]
pub(crate) fn translate_rplace_inner<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    body_id: BodyId,
    loc: Local,
    proj: &[rustc_middle::mir::PlaceElem<'tcx>],
) -> Exp {
    let mut inner = Exp::impure_var(ctx.translate_local(body_id, loc).ident());
    if proj.is_empty() {
        return inner;
    }

    use rustc_middle::mir::ProjectionElem::*;
    let mut place_ty = ctx.place_ty(body_id, Place::from(loc).as_ref());

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
                    inner = Call(Box::new(Exp::impure_qvar(acc)), vec![inner]);
                }
                TyKind::Tuple(fields) => {
                    let mut pat = vec![Wildcard; fields.len()];
                    pat[ix.as_usize()] = VarP("a".into());

                    inner = Let {
                        pattern: TupleP(pat),
                        arg: Box::new(inner),
                        body: Box::new(Exp::impure_var("a".into())),
                    }
                }
                TyKind::Closure(id, subst) => {
                    inner = Call(
                        Box::new(Exp::impure_qvar(names.accessor(*id, subst, 0, *ix))),
                        vec![inner],
                    );
                }
                e => unreachable!("{:?}", e),
            },
            Downcast(_, _) => {}
            Index(ix) => {
                // TODO: Use [_] syntax
                let ix_exp = Exp::impure_var(ctx.translate_local(body_id, *ix).ident());
                inner = Call(
                    Box::new(Exp::impure_qvar(QName::from_string("Slice.get").unwrap())),
                    vec![inner, ix_exp],
                )
            }
            ConstantIndex { .. } => unimplemented!("constant index projection"),
            Subslice { .. } => unimplemented!("subslice projection"),
            OpaqueCast(_) => unimplemented!("opaque cast projection"),
        }
        place_ty = place_ty.projection_ty(ctx.tcx, *elem);
    }

    inner
}
