use rustc_ast::Mutability;
use rustc_middle::ty::{Ty, TypingEnv};
use rustc_type_ir::TyKind;

use crate::{
    backend::ty::{AdtKind, classify_adt},
    ctx::Namer,
    translation::pearlite::{Ident, Pattern, Term},
};

use super::Why3Generator;

pub fn structural_resolve<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    subject: Ident,
    ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    let subject = Term::var(subject, ty);
    match ty.kind() {
        TyKind::Adt(adt, subst) => match classify_adt(ctx, names.source_id(), *adt, subst) {
            AdtKind::Unit | AdtKind::Empty | AdtKind::Snapshot(_) | AdtKind::Namespace => {
                Some(Term::true_(ctx.tcx))
            }
            AdtKind::Box(ty) | AdtKind::Ghost(ty) => {
                Some(resolve_of(ctx, names.typing_env(), subject.coerce(ty)))
            }
            AdtKind::Builtin(_) | AdtKind::Opaque { .. } => None,
            AdtKind::Transparent | AdtKind::PartiallyOpaque => {
                let arms = adt.variants().iter_enumerated().map(|(varidx, var)| {
                    let (fields, exps): (Vec<_>, Vec<_>) = var
                        .fields
                        .iter_enumerated()
                        .map(|(ix, f)| {
                            let sym = Ident::fresh_local(&format!("x{}", ix.as_usize()));
                            let fty = f.ty(ctx.tcx, subst);
                            (
                                (ix, Pattern::binder(sym, fty)),
                                resolve_of(ctx, names.typing_env(), Term::var(sym, fty)),
                            )
                        })
                        .unzip();

                    let body = exps.into_iter().rfold(Term::true_(ctx.tcx), Term::conj);
                    (Pattern::constructor(varidx, fields, ty), body)
                });
                Some(subject.match_(arms))
            }
        },
        TyKind::Tuple(tys) => {
            let (fields, exps): (Vec<_>, Vec<_>) = tys
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    let sym = Ident::fresh_local(&format!("x{i}"));
                    (
                        Pattern::binder(sym, ty),
                        resolve_of(ctx, names.typing_env(), Term::var(sym, ty)),
                    )
                })
                .unzip();
            let body = exps.into_iter().rfold(Term::true_(ctx.tcx), Term::conj);
            Some(Term::let_(Pattern::tuple(fields, ty), subject, body))
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
