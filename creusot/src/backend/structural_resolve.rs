use rustc_ast::Mutability;
use rustc_middle::ty::Ty;
use rustc_span::DUMMY_SP;
use rustc_type_ir::TyKind;

use crate::{
    backend::{
        Why3Generator,
        ty::{AdtKind, classify_adt},
    },
    ctx::Namer,
    translation::pearlite::{Ident, Pattern, Term, TermKind},
};

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
                Some(ctx.resolve(names.typing_env(), subject.coerce(ty)))
            }
            AdtKind::Builtin(_) | AdtKind::Opaque { .. } => None,
            AdtKind::Enum => {
                let arms = adt.variants().iter_enumerated().map(|(varidx, var)| {
                    let mut exp = Some(Term::true_(ctx.tcx));
                    let fields = var.fields.iter_enumerated().map(|(ix, f)| {
                        let sym = Ident::fresh_local(&format!("x{}", ix.as_usize()));
                        let fty = f.ty(ctx.tcx, subst);
                        exp = Some(
                            exp.take()
                                .unwrap()
                                .conj(ctx.resolve(names.typing_env(), Term::var(sym, fty))),
                        );
                        (ix, Pattern::binder(sym, fty))
                    });
                    (Pattern::constructor(varidx, fields, ty), exp.unwrap())
                });
                Some(subject.match_(arms))
            }
            AdtKind::Struct { partially_opaque } => {
                let mut exp = Term::true_(ctx.tcx);
                for (ix, f) in adt.non_enum_variant().fields.iter_enumerated() {
                    if f.vis.is_accessible_from(names.source_id(), ctx.tcx) {
                        let fty = f.ty(ctx.tcx, subst);
                        exp =
                            exp.conj(ctx.resolve(names.typing_env(), subject.clone().proj(ix, fty)))
                    }
                }
                if partially_opaque {
                    exp = exp.conj(Term {
                        kind: TermKind::PrivateResolve { term: Box::new(subject) },
                        ty: ctx.types.bool,
                        span: DUMMY_SP,
                    })
                }
                Some(exp)
            }
        },
        TyKind::Tuple(tys) => {
            let (fields, exps): (Vec<_>, Vec<_>) = tys
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    let sym = Ident::fresh_local(&format!("x{i}"));
                    (Pattern::binder(sym, ty), ctx.resolve(names.typing_env(), Term::var(sym, ty)))
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
