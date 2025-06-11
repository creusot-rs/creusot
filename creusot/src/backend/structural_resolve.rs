use rustc_ast::Mutability;
use rustc_middle::ty::{Ty, TypingEnv};
use rustc_span::DUMMY_SP;
use rustc_type_ir::TyKind;

use crate::{
    contracts_items::{get_builtin, is_trusted},
    translation::pearlite::{Ident, Pattern, Term, TermKind},
};

use super::Why3Generator;

pub fn structural_resolve<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subject: Ident,
    ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    let subject = Term::var(subject, ty);
    match ty.kind() {
        TyKind::Adt(adt, args) if adt.is_box() => {
            Some(resolve_of(ctx, typing_env, subject.coerce(args.type_at(0))))
        }
        TyKind::Adt(adt, _) if is_trusted(ctx.tcx, adt.did()) => None,
        TyKind::Adt(adt, args) => {
            assert!(get_builtin(ctx.tcx, adt.did()).is_none());
            let arms = adt
                .variants()
                .iter_enumerated()
                .map(|(varidx, var)| {
                    let (fields, exps): (Vec<_>, Vec<_>) = var
                        .fields
                        .iter_enumerated()
                        .map(|(ix, f)| {
                            let sym = Ident::fresh_local(&format!("x{}", ix.as_usize()));
                            let fty = f.ty(ctx.tcx, args);
                            (
                                (ix, Pattern::binder(sym, fty)),
                                resolve_of(ctx, typing_env, Term::var(sym, fty)),
                            )
                        })
                        .unzip();

                    let body = exps.into_iter().rfold(Term::true_(ctx.tcx), Term::conj);
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
                    let sym = Ident::fresh_local(&format!("x{i}"));
                    (Pattern::binder(sym, ty), resolve_of(ctx, typing_env, Term::var(sym, ty)))
                })
                .unzip();

            let body = exps.into_iter().rfold(Term::true_(ctx.tcx), Term::conj);

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
        _ => Some(Term::true_(ctx.tcx)),
    }
}

fn resolve_of<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    term: Term<'tcx>,
) -> Term<'tcx> {
    let Some((did, subst)) = ctx.resolve(typing_env, term.ty) else { return Term::true_(ctx.tcx) };
    Term::call_no_normalize(ctx.tcx, did, subst, [term])
}
