use rustc_ast::Mutability;
use rustc_middle::ty::{GenericArg, Ty};
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
        TyKind::Adt(adt, _) if is_snap_ty(ctx.tcx, adt.did()) => Some(Term::mk_true(ctx.tcx)),
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
                        .iter_enumerated()
                        .map(|(ix, f)| {
                            let sym = Symbol::intern(&format!("x{}", ix.as_usize()));
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
                .enumerate()
                .map(|(i, ty)| {
                    let sym = Symbol::intern(&format!("x{i}"));
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

fn resolve_of<'tcx>(ctx: &Why3Generator<'tcx>, term: Term<'tcx>) -> Term<'tcx> {
    let trait_meth_id = get_resolve_function(ctx.tcx);
    let substs = ctx.mk_args(&[GenericArg::from(term.ty)]);

    Term::call_no_normalize(ctx.tcx, trait_meth_id, substs, vec![term])
}
