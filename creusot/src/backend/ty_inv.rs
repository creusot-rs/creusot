use super::Why3Generator;
use crate::{
    contracts_items::{
        Intrinsic, get_builtin, is_ignore_structural_inv, is_opaque,
        is_tyinv_trivial_if_param_trivial,
    },
    ctx::TranslationCtx,
    naming::variable_name,
    translation::{
        pearlite::{Ident, Literal, Pattern, Term, TermKind, Trigger},
        traits::TraitResolved,
    },
};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_middle::ty::{GenericArg, Ty, TyKind, TypingEnv};
use rustc_span::Span;
use std::collections::HashSet;

/// # Errors
///
/// This will error (and stop the compilation) if an unsupported type is
/// encountered.
///
/// # Parameters
///
/// - `span`: used for error message
pub(crate) fn is_tyinv_trivial<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> bool {
    // we cannot use a TypeWalker as it does not visit ADT field types
    let mut visited_tys = HashSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        if !visited_tys.insert(ty) {
            continue;
        }

        let user_inv = resolve_user_inv(ctx, ty, typing_env);
        match user_inv {
            TraitResolved::NotATraitItem => unreachable!(),
            TraitResolved::NoInstance => (),
            TraitResolved::Instance { def: (uinv_did, _), .. }
                if is_tyinv_trivial_if_param_trivial(ctx.tcx, uinv_did) => {}
            _ => return false,
        }

        match ty.kind() {
            TyKind::Ref(_, ty, _) | TyKind::Slice(ty) | TyKind::Array(ty, _) => stack.push(*ty),
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(def, substs) if matches!(user_inv, TraitResolved::NoInstance) => {
                if is_opaque(ctx.tcx, def.did()) || get_builtin(ctx.tcx, def.did()).is_some() {
                    continue;
                }

                if def.is_enum() && def.variants().is_empty() {
                    return false;
                }

                stack.extend(def.all_fields().map(|f| f.ty(ctx.tcx, substs)))
            }

            // The instance is annotated with tyinv_trivial_if_param_trivial
            TyKind::Adt(_, substs) => stack.extend(substs.types()),

            TyKind::Closure(_, subst) => stack.extend(subst.as_closure().upvar_tys()),
            TyKind::Never | TyKind::Param(_) | TyKind::Alias(_, _) => return false,
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::FnDef(_, _)
            | TyKind::FnPtr(..)
            | TyKind::RawPtr(_, _)
            | TyKind::Dynamic(_, _) => (),
            _ => ctx.dcx().span_fatal(span, format!("Unsupported type: {ty}")),
        }
    }
    true
}

pub(crate) fn elaborate_inv<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> Option<(Term<'tcx>, bool)> {
    let x_ident = Ident::fresh_local("x").into();
    let subject = Term::var(x_ident, ty);
    let inv_id = Intrinsic::Inv.get(ctx);
    let subst = ctx.mk_args(&[GenericArg::from(ty)]);
    let lhs = Term::call(ctx.tcx, typing_env, inv_id, subst, [subject.clone()]);
    let trig = Box::new([Trigger(Box::new([lhs.clone()]))]);

    if is_tyinv_trivial(ctx, typing_env, ty, span) {
        return Some((
            lhs.eq(ctx.tcx, Term::true_(ctx.tcx)).forall_trig((x_ident, ty), trig),
            true,
        ));
    }

    let mut use_impl = false;

    let mut rhs = Term::true_(ctx.tcx);

    match resolve_user_inv(ctx, ty, typing_env) {
        TraitResolved::NotATraitItem => unreachable!(),
        TraitResolved::Instance { def, .. } => {
            rhs = rhs.conj(Term::call(ctx.tcx, typing_env, def.0, def.1, [subject.clone()]))
        }
        TraitResolved::UnknownFound => {
            rhs = rhs.conj(Term::call(
                ctx.tcx,
                typing_env,
                Intrinsic::Invariant.get(ctx),
                ctx.mk_args(&[GenericArg::from(ty)]),
                [subject.clone()],
            ))
        }
        TraitResolved::UnknownNotFound => use_impl = true,
        TraitResolved::NoInstance => (),
    }

    if matches!(ty.kind(), TyKind::Alias(..) | TyKind::Param(_)) {
        use_impl = true
    } else {
        rhs = rhs.conj(structural_invariant(ctx, typing_env, subject))
    }

    let term = if use_impl {
        if matches!(rhs.kind, TermKind::Lit(Literal::Bool(true))) {
            return None;
        }
        Term::implies(lhs, rhs)
    } else {
        lhs.eq(ctx.tcx, rhs)
    };

    Some((term.forall_trig((x_ident, ty), trig), !use_impl))
}

fn structural_invariant<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    term: Term<'tcx>,
) -> Term<'tcx> {
    if let TraitResolved::Instance { def, .. } = resolve_user_inv(ctx, term.ty, typing_env)
        && is_ignore_structural_inv(ctx.tcx, def.0)
    {
        return Term::true_(ctx.tcx);
    }

    match term.ty.kind() {
        TyKind::Adt(adt, _)
            if is_opaque(ctx.tcx, adt.did()) || get_builtin(ctx.tcx, adt.did()).is_some() =>
        {
            Term::true_(ctx.tcx)
        }
        TyKind::Adt(..) => build_inv_term_adt(ctx, typing_env, term),
        TyKind::Tuple(tys) => {
            let idsty: Vec<_> = tys
                .iter()
                .enumerate()
                .map(|(i, ty)| (Ident::fresh_local(format!("x{i}")), ty))
                .collect();
            let mut acc = Term::true_(ctx.tcx);
            for &(id, ty) in &idsty {
                conj_inv_call(ctx, typing_env, &mut acc, Term::var(id, ty))
            }
            let pattern =
                Pattern::tuple(idsty.iter().map(|&(id, ty)| Pattern::binder(id, ty)), term.ty);
            Term::let_(pattern, term, acc)
        }
        TyKind::Closure(_, substs) => {
            let idsty: Vec<_> = substs
                .as_closure()
                .upvar_tys()
                .iter()
                .enumerate()
                .map(|(i, ty)| (FieldIdx::from(i), Ident::fresh_local(format!("x{i}")), ty))
                .collect();
            let mut acc = Term::true_(ctx.tcx);
            for &(_, id, ty) in &idsty {
                conj_inv_call(ctx, typing_env, &mut acc, Term::var(id, ty))
            }
            let pattern = Pattern::constructor(
                VariantIdx::ZERO,
                idsty.iter().map(|&(fld, id, ty)| (fld, Pattern::binder(id, ty))),
                term.ty,
            );
            Term::let_(pattern, term, acc)
        }
        _ => unreachable!(),
    }
}

pub(crate) fn inv_call<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    term: Term<'tcx>,
) -> Option<Term<'tcx>> {
    let ty = ctx.normalize_erasing_regions(typing_env, term.ty);
    if is_tyinv_trivial(&ctx, typing_env, ty, term.span) {
        return None;
    }
    let subst = ctx.mk_args(&[GenericArg::from(ty)]);
    Some(Term::call(ctx.tcx, typing_env, Intrinsic::Inv.get(ctx), subst, [term]))
}

fn conj_inv_call<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    acc: &mut Term<'tcx>,
    term: Term<'tcx>,
) {
    if let Some(inv) = inv_call(ctx, typing_env, term) {
        let t = std::mem::replace(acc, Term::unit(ctx.tcx) /* Dummy */);
        *acc = t.conj(inv)
    }
}

fn build_inv_term_adt<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    term: Term<'tcx>,
) -> Term<'tcx> {
    let TyKind::Adt(adt_def, substs) = term.ty.kind() else {
        unreachable!("asked to build ADT invariant for non-ADT type {:?}", term.ty)
    };

    if adt_def.variants().is_empty() {
        return Term::false_(ctx.tcx);
    }
    let arms = adt_def.variants().iter_enumerated().map(move |(var_idx, var_def)| {
        let tuple_var = var_def.ctor.is_some();

        let mut exp = Term::true_(ctx.tcx);
        let fields = var_def.fields.iter().enumerate().map(|(field_idx, field_def)| {
            let field_name = if tuple_var {
                Ident::fresh_local(format!("a_{field_idx}"))
            } else {
                Ident::fresh_local(variable_name(field_def.ident(ctx.tcx).name.as_str()))
            };

            let field_ty = field_def.ty(ctx.tcx, substs);

            conj_inv_call(ctx, typing_env, &mut exp, Term::var(field_name, field_ty));
            (field_idx.into(), Pattern::binder(field_name, field_ty))
        });

        (Pattern::constructor(var_idx, fields, term.ty), exp)
    });
    term.match_(arms)
}

fn resolve_user_inv<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    ty: Ty<'tcx>,
    typing_env: TypingEnv<'tcx>,
) -> TraitResolved<'tcx> {
    TraitResolved::resolve_item(
        ctx.tcx,
        typing_env,
        Intrinsic::Invariant.get(ctx),
        ctx.mk_args(&[GenericArg::from(ty)]),
    )
}
