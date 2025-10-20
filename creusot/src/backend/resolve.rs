use std::collections::HashSet;

use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, Ty, TypingEnv};
use rustc_span::{DUMMY_SP, Span};
use rustc_type_ir::TyKind;

use crate::{
    backend::{
        Why3Generator,
        ty::{AdtKind, classify_adt},
    },
    contracts_items::{Intrinsic, is_trivial_if_param_trivial},
    ctx::{Namer, TranslationCtx},
    translation::{
        pearlite::{Ident, Pattern, Term, TermKind, Trigger},
        traits::TraitResolved,
    },
};

pub fn is_resolve_trivial<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    scope: DefId,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> bool {
    let mut visited_tys = HashSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        if !visited_tys.insert(ty) {
            continue;
        }

        match resolve_user_resolve(ctx, ty, typing_env) {
            TraitResolved::NotATraitItem => unreachable!(),
            TraitResolved::NoInstance => {}
            TraitResolved::Instance { def, .. } if is_trivial_if_param_trivial(ctx.tcx, def.0) => {
                match ty.kind() {
                    TyKind::Ref(_, _, Mutability::Not) => {}
                    TyKind::Slice(ty) | TyKind::Array(ty, _) => stack.push(*ty),
                    TyKind::Adt(_, subst) => stack.extend(subst.types()),
                    _ => unreachable!(),
                }
                continue;
            }
            _ => return false,
        }

        match ty.kind() {
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(def, subst) => match classify_adt(ctx, scope, *def, subst) {
                AdtKind::Namespace
                | AdtKind::Snapshot(_)
                | AdtKind::Unit
                | AdtKind::Builtin(_)
                | AdtKind::Empty => (),
                AdtKind::Struct { partially_opaque: true } | AdtKind::Opaque { .. } => {
                    return false;
                }
                AdtKind::Box(ty) | AdtKind::Ghost(ty) => stack.push(ty),
                AdtKind::Enum | AdtKind::Struct { partially_opaque: false } => {
                    stack.extend(def.all_fields().map(|f| f.ty(ctx.tcx, subst)))
                }
            },
            TyKind::Closure(_, subst) => stack.extend(subst.as_closure().upvar_tys()),
            TyKind::Param(_)
            | TyKind::Alias(_, _)
            | TyKind::Dynamic(..)
            | TyKind::Ref(_, _, Mutability::Mut) => return false,
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::FnDef(..)
            | TyKind::FnPtr(..)
            | TyKind::RawPtr(..)
            | TyKind::Never
            | TyKind::Ref(_, _, Mutability::Not) => (),
            _ => ctx.dcx().span_fatal(span, format!("Unsupported type: {ty}")),
        }
    }

    true
}

pub fn structural_resolve<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    subject: Term<'tcx>,
    span: Span,
) -> Option<Term<'tcx>> {
    let ty = subject.ty;

    if is_resolve_trivial(ctx, names.source_id(), names.typing_env(), ty, span) {
        return Some(Term::true_(ctx.tcx));
    }

    match ty.kind() {
        TyKind::Adt(adt, subst) => match classify_adt(ctx, names.source_id(), *adt, subst) {
            AdtKind::Box(ty) | AdtKind::Ghost(ty) => {
                Some(ctx.resolve(names.source_id(), names.typing_env(), subject.coerce(ty)))
            }
            AdtKind::Opaque { .. } | AdtKind::Builtin(_) => None,
            AdtKind::Enum => {
                let arms = adt.variants().iter_enumerated().map(|(varidx, var)| {
                    let mut exp = Some(Term::true_(ctx.tcx));
                    let fields = var.fields.iter_enumerated().map(|(ix, f)| {
                        let sym = Ident::fresh_local(&format!("x{}", ix.as_usize()));
                        let fty = f.ty(ctx.tcx, subst);
                        exp = Some(exp.take().unwrap().conj(ctx.resolve(
                            names.source_id(),
                            names.typing_env(),
                            Term::var(sym, fty),
                        )));
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
                        exp = exp.conj(ctx.resolve(
                            names.source_id(),
                            names.typing_env(),
                            subject.clone().proj(ix, fty),
                        ))
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
            AdtKind::Unit | AdtKind::Empty | AdtKind::Snapshot(_) | AdtKind::Namespace => {
                Some(Term::true_(ctx.tcx))
            }
        },
        TyKind::Tuple(tys) => {
            let mut exp = Term::true_(ctx.tcx);
            for (i, ty) in tys.iter().enumerate() {
                exp = exp.conj(ctx.resolve(
                    names.source_id(),
                    names.typing_env(),
                    subject.clone().proj(i.into(), ty),
                ))
            }
            Some(exp)
        }
        TyKind::Ref(_, _, Mutability::Mut) => {
            Some(subject.clone().fin().eq(ctx.tcx, subject.cur()))
        }
        TyKind::Closure(_, subst) => {
            let mut exp = Term::true_(ctx.tcx);
            let csubst = subst.as_closure();
            for (ix, ty) in csubst.upvar_tys().iter().enumerate() {
                exp = ctx
                    .resolve(
                        names.source_id(),
                        names.typing_env(),
                        subject.clone().proj(ix.into(), ty),
                    )
                    .conj(exp)
            }
            Some(exp)
        }
        TyKind::Alias(..) | TyKind::Param(_) | TyKind::Array(..) | TyKind::Slice(..) => None,
        ty => unreachable!("{ty:?}"),
    }
}

pub enum ResolveDef<'tcx> {
    None,
    Body(Ident, Term<'tcx>),
    Axiom { axiom: Term<'tcx>, rewrite: bool },
}

pub(crate) fn elaborate_resolve_def<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> ResolveDef<'tcx> {
    let x_ident = Ident::fresh_local("x");
    let subject = Term::var(x_ident, ty);

    if is_resolve_trivial(ctx, names.source_id(), names.typing_env(), ty, span) {
        return ResolveDef::Body(x_ident, Term::true_(ctx.tcx));
    }

    let mut use_impl = false;
    let mut rhs = Term::true_(ctx.tcx);
    match resolve_user_resolve(ctx, ty, names.typing_env()) {
        TraitResolved::NotATraitItem => unreachable!(),
        TraitResolved::Instance { def, .. } => {
            if !matches!(ty.kind(), TyKind::Ref(..)) && !ty.is_box() {
                rhs = rhs.conj(Term::call(
                    ctx.tcx,
                    names.typing_env(),
                    def.0,
                    def.1,
                    [subject.clone()],
                ))
            }
        }
        TraitResolved::UnknownFound => {
            rhs = rhs.conj(Term::call(
                ctx.tcx,
                names.typing_env(),
                Intrinsic::ResolveMethod.get(ctx),
                ctx.mk_args(&[GenericArg::from(ty)]),
                [subject.clone()],
            ))
        }
        TraitResolved::UnknownNotFound => use_impl = true,
        TraitResolved::NoInstance => (),
    }

    if let Some(sres) = structural_resolve(ctx, names, subject.clone(), span) {
        rhs = rhs.conj(sres)
    } else {
        use_impl = true
    }

    if use_impl && rhs.is_true() {
        return ResolveDef::None;
    }

    let mut use_axiom = use_impl;
    if let TyKind::Adt(def, subst) = ty.kind()
        && matches!(
            classify_adt(ctx, names.source_id(), *def, subst),
            AdtKind::Opaque { .. } | AdtKind::Struct { .. } | AdtKind::Enum
        )
    {
        use_axiom = true;
    }

    if use_axiom {
        let lhs = Term::call(
            ctx.tcx,
            names.typing_env(),
            Intrinsic::Resolve.get(ctx),
            ctx.mk_args(&[GenericArg::from(ty)]),
            [subject],
        );
        let term =
            if use_impl { Term::implies(lhs.clone(), rhs) } else { lhs.clone().eq(ctx.tcx, rhs) };

        ResolveDef::Axiom {
            axiom: term.forall_trig((x_ident.into(), ty), [Trigger(Box::new([lhs]))]),
            rewrite: !use_impl,
        }
    } else {
        ResolveDef::Body(x_ident, rhs)
    }
}

fn resolve_user_resolve<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    ty: Ty<'tcx>,
    typing_env: TypingEnv<'tcx>,
) -> TraitResolved<'tcx> {
    TraitResolved::resolve_item(
        ctx.tcx,
        typing_env,
        Intrinsic::ResolveMethod.get(ctx),
        ctx.mk_args(&[GenericArg::from(ty)]),
    )
}
