use rustc_ast::Mutability;
use rustc_middle::ty::{GenericArg, Ty};
use rustc_span::{DUMMY_SP, Symbol};
use rustc_type_ir::TyKind;

use crate::{
    contracts_items::{get_builtin, get_resolve_function, is_snap_ty, is_trusted},
    pearlite::{Pattern, Term, TermKind},
};

use super::Why3Generator;

pub fn structural_resolve<'tcx>(
    ctx: &Why3Generator<'tcx>,
    subject: Symbol,
    ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    let subject = Term::var(subject, ty);
    match ty.kind() {
        TyKind::Adt(adt, args) if adt.is_box() => {
            Some(resolve_of(ctx, subject.coerce(args.type_at(0))))
        }
        TyKind::Adt(adt, _) if is_trusted(ctx.tcx, adt.did()) => None,
        TyKind::Adt(adt, _) if is_snap_ty(ctx.tcx, adt.did()) => Some(Term::mk_true(ctx.tcx)),
        TyKind::Adt(adt, _) if get_builtin(ctx.tcx, adt.did()).is_some() => {
            Some(Term::mk_true(ctx.tcx))
        }
        TyKind::Adt(adt, args) => {
            let arms = adt
                .variants()
                .iter_enumerated()
                .map(|(varidx, var)| {
                    let (fields, exps): (Vec<_>, Vec<_>) = var
                        .fields
                        .iter_enumerated()
                        .map(|(ix, f)| {
                            let sym = Symbol::intern(&format!("x{}", ix.as_usize()));
                            let fty = f.ty(ctx.tcx, args);
                            (Pattern::binder(sym, fty), resolve_of(ctx, Term::var(sym, fty)))
                        })
                        .unzip();

                    let body = exps.into_iter().rfold(Term::mk_true(ctx.tcx), Term::conj);
                    (Pattern::constructor(varidx, fields, ty), body)
                })
                .collect();

            Some(Term {
                ty: ctx.types.bool,
                kind: TermKind::Match { scrutinee: Box::new(subject), arms },
                span: DUMMY_SP,
            })
        }
        TyKind::Tuple(tys) => {
            let (fields, exps): (Vec<_>, Vec<_>) = tys
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    let sym = Symbol::intern(&format!("x{i}"));
                    (Pattern::binder(sym, ty), resolve_of(ctx, Term::var(sym, ty)))
                })
                .unzip();

            let body = exps.into_iter().rfold(Term::mk_true(ctx.tcx), Term::conj);

            Some(Term {
                ty: ctx.types.bool,
                kind: TermKind::Match {
                    scrutinee: Box::new(subject),
                    arms: Box::new([(Pattern::tuple(fields, ty), body)]),
                },
                span: DUMMY_SP,
            })
        }
        TyKind::Ref(_, _, Mutability::Mut) => {
            Some(subject.clone().fin().eq(ctx.tcx, subject.cur()))
        }
        TyKind::Closure(..) | TyKind::Param(_) => None,
        _ => Some(Term::mk_true(ctx.tcx)),
    }
}

fn resolve_of<'tcx>(ctx: &Why3Generator<'tcx>, term: Term<'tcx>) -> Term<'tcx> {
    let trait_meth_id = get_resolve_function(ctx.tcx);
    let substs = ctx.mk_args(&[GenericArg::from(term.ty)]);

    Term::call_no_normalize(ctx.tcx, trait_meth_id, substs, [term])
}
