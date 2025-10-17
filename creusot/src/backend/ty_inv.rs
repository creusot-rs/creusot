use super::Why3Generator;
use crate::{
    backend::ty::{AdtKind, classify_adt},
    contracts_items::{
        Intrinsic, is_ignore_structural_inv, is_open_inv_result, is_tyinv_trivial_if_param_trivial,
    },
    ctx::{Namer, TranslationCtx},
    naming::{name, variable_name},
    translation::{
        pearlite::{Ident, Literal, Pattern, Term, TermKind, Trigger},
        specification::{Condition, PreSignature},
        traits::TraitResolved,
    },
};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::{def::DefKind, def_id::DefId};
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
    scope: DefId,
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

        // Handle user invariant
        match resolve_user_inv(ctx, ty, typing_env) {
            TraitResolved::NotATraitItem => unreachable!(),
            TraitResolved::NoInstance => {}
            TraitResolved::Instance { def, .. }
                if is_tyinv_trivial_if_param_trivial(ctx.tcx, def.0) =>
            {
                match ty.kind() {
                    TyKind::Ref(_, ty, _) | TyKind::Slice(ty) | TyKind::Array(ty, _) => {
                        stack.push(*ty)
                    }
                    TyKind::Adt(_, subst) => stack.extend(subst.types()),
                    _ => unreachable!(),
                }
                if is_ignore_structural_inv(ctx.tcx, def.0) {
                    continue;
                }
            }
            _ => return false,
        }

        // Handle structural invariant
        match ty.kind() {
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(def, subst) => match classify_adt(ctx, scope, *def, subst) {
                AdtKind::Namespace
                | AdtKind::Snapshot(_)
                | AdtKind::Opaque { always: true }
                | AdtKind::Unit
                | AdtKind::Builtin(_) => continue,
                AdtKind::Opaque { always: false } | AdtKind::Empty => return false,
                AdtKind::Transparent | AdtKind::PartiallyOpaque => {
                    stack.extend(def.all_fields().map(|f| f.ty(ctx.tcx, subst)))
                }
                _ => unreachable!(),
            },
            TyKind::Closure(_, subst) => stack.extend(subst.as_closure().upvar_tys()),
            TyKind::Param(_) | TyKind::Alias(_, _) => return false,
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::FnDef(..)
            | TyKind::FnPtr(..)
            | TyKind::RawPtr(..)
            | TyKind::Dynamic(..) => (),
            _ => ctx.dcx().span_fatal(span, format!("Unsupported type: {ty}")),
        }
    }
    true
}

pub(crate) fn elaborate_inv<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> Option<(Term<'tcx>, bool)> {
    let x_ident = Ident::fresh_local("x").into();
    let subject = Term::var(x_ident, ty);
    let inv_id = Intrinsic::Inv.get(ctx);
    let subst = ctx.mk_args(&[GenericArg::from(ty)]);
    let lhs = Term::call(ctx.tcx, names.typing_env(), inv_id, subst, [subject.clone()]);
    let trig = Box::new([Trigger(Box::new([lhs.clone()]))]);

    if is_tyinv_trivial(ctx, names.source_id(), names.typing_env(), ty, span) {
        return Some((
            lhs.eq(ctx.tcx, Term::true_(ctx.tcx)).forall_trig((x_ident, ty), trig),
            true,
        ));
    }

    let mut use_impl = false;

    let mut rhs = Term::true_(ctx.tcx);

    match resolve_user_inv(ctx, ty, names.typing_env()) {
        TraitResolved::NotATraitItem => unreachable!(),
        TraitResolved::Instance { def, .. } => {
            rhs = rhs.conj(Term::call(ctx.tcx, names.typing_env(), def.0, def.1, [subject.clone()]))
        }
        TraitResolved::UnknownFound => {
            rhs = rhs.conj(Term::call(
                ctx.tcx,
                names.typing_env(),
                Intrinsic::Invariant.get(ctx),
                ctx.mk_args(&[GenericArg::from(ty)]),
                [subject.clone()],
            ))
        }
        TraitResolved::UnknownNotFound => use_impl = true,
        TraitResolved::NoInstance => (),
    }

    if !matches!(ty.kind(), TyKind::Alias(..) | TyKind::Param(_))
        && let Some(sinv) = structural_invariant(ctx, names, subject)
    {
        rhs = rhs.conj(sinv)
    } else {
        use_impl = true
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
    names: &impl Namer<'tcx>,
    term: Term<'tcx>,
) -> Option<Term<'tcx>> {
    if let TraitResolved::Instance { def, .. } = resolve_user_inv(ctx, term.ty, names.typing_env())
        && is_ignore_structural_inv(ctx.tcx, def.0)
    {
        return Some(Term::true_(ctx.tcx));
    }

    match term.ty.kind() {
        TyKind::Adt(..) => build_inv_term_adt(ctx, names, term),
        TyKind::Tuple(tys) => {
            let idsty: Vec<_> = tys
                .iter()
                .enumerate()
                .map(|(i, ty)| (Ident::fresh_local(format!("x{i}")), ty))
                .collect();
            let mut acc = Term::true_(ctx.tcx);
            for &(id, ty) in &idsty {
                conj_inv_call(ctx, names, &mut acc, Term::var(id, ty))
            }
            let pattern =
                Pattern::tuple(idsty.iter().map(|&(id, ty)| Pattern::binder(id, ty)), term.ty);
            Some(Term::let_(pattern, term, acc))
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
                conj_inv_call(ctx, names, &mut acc, Term::var(id, ty))
            }
            let pattern = Pattern::constructor(
                VariantIdx::ZERO,
                idsty.iter().map(|&(fld, id, ty)| (fld, Pattern::binder(id, ty))),
                term.ty,
            );
            Some(Term::let_(pattern, term, acc))
        }
        _ => unreachable!(),
    }
}

pub(crate) fn inv_call<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    scope_id: DefId,
    term: Term<'tcx>,
) -> Option<Term<'tcx>> {
    let ty = ctx.normalize_erasing_regions(typing_env, term.ty);
    if is_tyinv_trivial(&ctx, scope_id, typing_env, ty, term.span) {
        return None;
    }
    let subst = ctx.mk_args(&[GenericArg::from(ty)]);
    Some(Term::call(ctx.tcx, typing_env, Intrinsic::Inv.get(ctx), subst, [term]))
}

fn conj_inv_call<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    acc: &mut Term<'tcx>,
    term: Term<'tcx>,
) {
    if let Some(inv) = inv_call(ctx, names.typing_env(), names.source_id(), term) {
        let t = std::mem::replace(acc, Term::unit(ctx.tcx) /* Dummy */);
        *acc = t.conj(inv)
    }
}

fn build_inv_term_adt<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    term: Term<'tcx>,
) -> Option<Term<'tcx>> {
    let TyKind::Adt(def, subst) = term.ty.kind() else { unreachable!() };
    match classify_adt(ctx, names.source_id(), *def, subst) {
        AdtKind::Empty => return Some(Term::false_(ctx.tcx)),
        AdtKind::Opaque { always: true }
        | AdtKind::Unit
        | AdtKind::Snapshot(_)
        | AdtKind::Namespace
        | AdtKind::Builtin(_) => return Some(Term::true_(ctx.tcx)),
        AdtKind::Opaque { always: false } => return None,
        AdtKind::Transparent | AdtKind::PartiallyOpaque => (),
        _ => unreachable!(),
    }

    let arms = def.variants().iter_enumerated().map(move |(var_idx, var_def)| {
        let tuple_var = var_def.ctor.is_some();

        let mut exp = Term::true_(ctx.tcx);
        let fields = var_def.fields.iter().enumerate().map(|(field_idx, field_def)| {
            let field_name = if tuple_var {
                Ident::fresh_local(format!("a_{field_idx}"))
            } else {
                Ident::fresh_local(variable_name(field_def.ident(ctx.tcx).name.as_str()))
            };

            let field_ty = field_def.ty(ctx.tcx, subst);

            conj_inv_call(ctx, names, &mut exp, Term::var(field_name, field_ty));
            (field_idx.into(), Pattern::binder(field_name, field_ty))
        });

        (Pattern::constructor(var_idx, fields, term.ty), exp)
    });
    Some(term.match_(arms))
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

pub(crate) fn sig_add_type_invariant_spec<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    scope_id: DefId,
    pre_sig: &mut PreSignature<'tcx>,
    def_id: DefId,
) {
    let fn_name = ctx.opt_item_name(def_id);
    let fn_name = match &fn_name {
        Some(fn_name) => fn_name.as_str(),
        None => "closure",
    };

    let params_open_inv: HashSet<usize> = ctx
        .params_open_inv(def_id)
        .iter()
        .copied()
        .flatten()
        .map(|&i| if ctx.is_closure_like(def_id) { i + 1 } else { i })
        .collect();

    let new_requires = pre_sig.inputs.iter().enumerate().filter_map(|(i, (ident, span, ty))| {
        if !params_open_inv.contains(&i)
            && let Some(term) = inv_call(ctx, typing_env, scope_id, Term::var(ident.0, *ty))
        {
            let expl = format!("expl:{} '{}' type invariant", fn_name, ident.0.name().to_string());
            Some(Condition { term: term.span(*span), expl })
        } else {
            None
        }
    });
    pre_sig.contract.requires.splice(0..0, new_requires);

    let ret_ty_span: Option<Span> = try { ctx.hir_get_fn_output(def_id.as_local()?)?.span() };
    if (ctx.def_kind(def_id) == DefKind::ConstParam || !is_open_inv_result(ctx.tcx, def_id))
        && let Some(term) =
            inv_call(ctx, typing_env, scope_id, Term::var(name::result(), pre_sig.output))
    {
        let expl = format!("expl:{} result type invariant", fn_name);
        pre_sig.contract.ensures.insert(
            0,
            Condition {
                term: term.span(ret_ty_span.unwrap_or_else(|| ctx.def_span(def_id))),
                expl,
            },
        );
    }
}
