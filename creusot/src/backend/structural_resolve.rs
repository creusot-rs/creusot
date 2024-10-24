use rustc_ast::Mutability;
use rustc_middle::ty::{GenericArg, GenericArgs, GenericArgsRef, Ty, TyCtxt};
use rustc_span::{Symbol, DUMMY_SP};
use rustc_type_ir::TyKind;

use crate::{
    contracts_items::{get_builtin, get_resolve_function, is_snap_ty, is_trusted},
    pearlite::{BinOp, Pattern, Term, TermKind},
};

use super::Why3Generator;

pub fn structural_resolve<'tcx>(
    ctx: &Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> ((Symbol, Ty<'tcx>), Option<Term<'tcx>>) {
    let subject = Term::var(Symbol::intern("x"), ty);
    let body = match ty.kind() {
        TyKind::Adt(adt, _) if adt.is_box() => Some(resolve_of(ctx, subject.cur())),
        TyKind::Adt(adt, _) if is_trusted(ctx.tcx, adt.did()) => None,
        TyKind::Adt(_, _) if is_snap_ty(ctx.tcx, ty) => Some(Term::mk_true(ctx.tcx)),
        TyKind::Adt(adt, _) if get_builtin(ctx.tcx, adt.did()).is_some() => {
            Some(Term::mk_true(ctx.tcx))
        }
        TyKind::Adt(adt, args) => {
            let arms = adt
                .variants()
                .into_iter()
                .map(|var| {
                    let (fields, exps): (_, Vec<_>) = var
                        .fields
                        .iter()
                        .zip('a'..)
                        .map(|(f, id)| {
                            let sym = Symbol::intern(&id.to_string());
                            let var = Term::var(sym, f.ty(ctx.tcx, args));
                            (Pattern::Binder(sym), resolve_of(ctx, var))
                        })
                        .unzip();

                    let body = exps.into_iter().rfold(Term::mk_true(ctx.tcx), Term::conj);
                    (Pattern::Constructor { variant: var.def_id, substs: args, fields }, body)
                })
                .collect();

            Some(Term {
                ty: ctx.types.bool,
                kind: TermKind::Match { scrutinee: Box::new(subject), arms },
                span: DUMMY_SP,
            })
        }
        TyKind::Tuple(tys) => {
            let (fields, exps): (_, Vec<_>) = tys
                .iter()
                .zip('a'..)
                .map(|(ty, id)| {
                    let sym = Symbol::intern(&id.to_string());
                    let var = Term::var(sym, ty);
                    (Pattern::Binder(sym), resolve_of(ctx, var))
                })
                .unzip();

            let body = exps.into_iter().rfold(Term::mk_true(ctx.tcx), Term::conj);

            Some(Term {
                ty: ctx.types.bool,
                kind: TermKind::Match {
                    scrutinee: Box::new(subject),
                    arms: vec![(Pattern::Tuple(fields), body)],
                },
                span: DUMMY_SP,
            })
        }
        TyKind::Ref(_, _, Mutability::Mut) => {
            Some(subject.clone().fin().bin_op(ctx.tcx, BinOp::Eq, subject.cur()))
        }
        TyKind::Param(_) => None,
        _ => Some(Term::mk_true(ctx.tcx)),
    };

    ((Symbol::intern("x"), ty), body)
}

// Rewrite a type as a "head type" and a ssusbtitution, such that the head type applied to the substitution
// equals the type.
// The head type is used as a dependency node.
pub(crate) fn head_and_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> (Ty<'tcx>, GenericArgsRef<'tcx>) {
    match ty.kind() {
        TyKind::Adt(adt_def, subst) => {
            (Ty::new_adt(tcx, *adt_def, GenericArgs::identity_for_item(tcx, adt_def.did())), subst)
        }
        TyKind::Closure(did, _) => (ty, GenericArgs::identity_for_item(tcx, tcx.parent(*did))),
        TyKind::Tuple(tys) => {
            let params = (0..tys.len())
                .map(|i| Ty::new_param(tcx, i as _, Symbol::intern(&format!("T{i}"))));
            let tup = Ty::new_tup_from_iter(tcx, params);
            let subst = tcx.mk_args_from_iter(tys.iter().map(GenericArg::from));
            (tup, subst)
        }
        TyKind::Alias(..) | TyKind::Param(_) => (
            Ty::new_param(tcx, 0, Symbol::intern(&format!("T"))),
            tcx.mk_args(&[GenericArg::from(ty)]),
        ),
        TyKind::RawPtr(_, _) => (
            Ty::new_param(tcx, 0, Symbol::intern(&format!("T"))),
            tcx.mk_args(&[GenericArg::from(ty)]),
        ),
        TyKind::Ref(_, ty, mutbl) => {
            let p = Ty::new_param(tcx, 0, Symbol::intern(&format!("T")));

            (
                Ty::new_ref(tcx, tcx.lifetimes.re_erased, p, *mutbl),
                tcx.mk_args(&[GenericArg::from(*ty)]),
            )
        }
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => {
            (ty, GenericArgs::empty())
        }
        _ => unimplemented!("{ty:?}"), // TODO
    }
}

fn resolve_of<'tcx>(ctx: &Why3Generator<'tcx>, term: Term<'tcx>) -> Term<'tcx> {
    let trait_meth_id = get_resolve_function(ctx.tcx);
    let substs = ctx.mk_args(&[GenericArg::from(term.ty)]);

    Term::call(ctx.tcx, trait_meth_id, substs, vec![term])
}
