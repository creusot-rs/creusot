use crate::{
    ctx::TranslationCtx,
    translation::pearlite::{MapSubstitution, Substable, Term, TermKind},
    util::erased_identity_for_item,
};
use itertools::{EitherOrBoth, Itertools};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{
    EarlyBinder, GenericArg, GenericArgsRef, TyCtxt, TypingEnv,
    fast_reject::{TreatParams, simplify_type},
};
use rustc_span::Span;
use rustc_type_ir::GenericArgKind;

pub(crate) fn get_logic_id(ctx: &TranslationCtx, def_id: DefId) -> DefId {
    let ensures_body = ctx.raw_term(def_id).expect("no ensures clause associated with this alias");

    match &ensures_body.1.kind {
        TermKind::Binary { rhs, .. } => match &rhs.kind {
            TermKind::Call { id, .. } => *id,
            _ => unreachable!("this should be a function call"),
        },
        _ => unreachable!("this should be an equality"),
    }
}

pub(crate) fn subst_call<'tcx, Args>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    prog_id: DefId,
    prog_subst: GenericArgsRef<'tcx>,
    prog_args: Args,
) -> Option<(DefId, Box<[Term<'tcx>]>, GenericArgsRef<'tcx>)>
where
    Args: IntoIterator<Item = Term<'tcx>>,
{
    if let Some((_, alias_id)) = ctx.logic_alias(prog_id) {
        let ensures_body =
            ctx.raw_term(alias_id).expect("no ensures clause associated with this alias");

        match &ensures_body.1.kind {
            TermKind::Binary { rhs, .. } => match &rhs.kind {
                TermKind::Call { id, args, subst: call_subst } => {
                    let mut args_subst = MapSubstitution::new();

                    let prog_params = &ensures_body.0;
                    for (param, term) in
                        itertools::zip_eq(&prog_params[..prog_params.len() - 1], prog_args)
                    {
                        args_subst.insert(param.0, term.kind);
                    }

                    let helper_subst = |mut term: Term<'tcx>| {
                        term = ctx.normalize_erasing_regions(
                            typing_env,
                            EarlyBinder::bind(ctx.tcx, term).instantiate(ctx.tcx, prog_subst),
                        );
                        term.subst(&args_subst);
                        term
                    };

                    let call_subst = ctx.normalize_erasing_regions(
                        typing_env,
                        EarlyBinder::bind(ctx.tcx, *call_subst).instantiate(ctx.tcx, prog_subst),
                    );

                    let res_args = args.iter().map(|term| helper_subst(term.clone())).collect();
                    Some((*id, res_args, call_subst))
                }
                _ => unreachable!("this should be a function call"),
            },
            _ => unreachable!("this should be an equality"),
        }
    } else {
        None
    }
}

fn impl_this_trait(ctx: &TranslationCtx, impl_id: DefId, trait_id: DefId) -> bool {
    // FIXME?: Is there a better way to do this ?
    let Some(sty) = simplify_type(
        ctx.tcx,
        ctx.tcx.type_of(impl_id).skip_binder(),
        TreatParams::InstantiateWithInfer,
    ) else {
        return false;
    };

    ctx.trait_impls_of(trait_id).non_blanket_impls().iter().find(|(ty, _)| **ty == sty).is_some()
}

fn failwith(
    tcx: TyCtxt<'_>,
    msg: impl ToString,
    prog_span: Span,
    alias_span: Span,
    logic_span: Span,
) -> ! {
    tcx.dcx()
        .struct_span_err(alias_span, msg.to_string())
        .with_span_note(prog_span, "function defined here")
        .with_span_note(logic_span, "logic function defined here")
        .emit()
        .raise_fatal()
}

/*
 * TODO mael: write doc
 *
 * +--------------------------------------------------------------------------------------------+
 * |    Program part   |    Logic part     |                    Validity                        |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  fun              |  fun              |  valid if both fun comes from the current crate,   |
 * |                   |                   |     or are located in an extern_spec!              |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  fun              |   trait           |    invalid                                         |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  fun              |   impl type       |    invalid                                         |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  fun              |   impl trait      |    invalid                                         |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  trait            |   fun             |    valid if `fun` comes from the current crate     |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  trait            |   trait           |    valid if in the same trait                      |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  trait            |   impl type       |    valid if `type` also implement `trait`          |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  trait            |   impl trait      |    valid if it's the same trait                    |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl type        |   fun             |    valid if `fun` comes from the current crate     |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl type        |   trait           |    valid if `type` implements `trait`              |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl type        |   impl type       |    valid if it's the same type (*)                 |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl type        |   impl trait      |    valid if it's the same type                     |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl trait       |   fun             |    valid if `fun` comes from the current crate     |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl trait       |   trait           |    valid if it's the same trait                    |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl trait       |   impl type       |    valid if `type` implements `trait`              |
 * |-------------------+-------------------+----------------------------------------------------|
 * |  impl trait       |   impl trait      |    valid if it's the same trait                    |
 * +-------------------+-------------------+----------------------------------------------------+
 *
 * (*) I'm not sure if this is really a big deal to have aliasing between methods from two
 * different types. Maybe we could to allow it as long as the signatures match?
 */
pub(crate) fn check_validity(
    ctx: &TranslationCtx,
    prog_id: DefId,
    alias_id: DefId,
    alias_span: Span,
) {
    let tcx = ctx.tcx;
    let logic_id = get_logic_id(ctx, alias_id);

    let prog_span = tcx.def_span(prog_id);
    let logic_span = tcx.def_span(logic_id);

    // If items are in an extern_spec! get their real DefId (we currently
    // have the DefId of their correspondig items in the extern_spec!)
    let real_prog_id = ctx.extern_spec_items(prog_id).unwrap_or(prog_id);
    let real_logic_id = ctx.extern_spec_items(logic_id).unwrap_or(logic_id);

    let prog_subst = erased_identity_for_item(tcx, real_prog_id);
    let logic_subst = erased_identity_for_item(tcx, real_logic_id);

    let prog_parent = tcx.assoc_parent(real_prog_id);
    let logic_parent = tcx.assoc_parent(real_logic_id);

    // The logic alias must come from the current crate.
    // If the logic alias is in an extern_spec!, logic_id is the
    // DefId of the corresponding item in the extern_spec! so the tests will succeed.
    if !logic_id.is_local() {
        failwith(
            tcx,
            "The logic function must be defined in the same crate as the aliased program function.",
            prog_span,
            alias_span,
            logic_span,
        )
    }

    match (prog_parent, logic_parent) {
        (None, None) => {
            // program function aliased by another program function.
            // already checked the requirements at this point.
        }
        (None, _) => failwith(
            tcx,
            "A program function can only be aliased by another program function.",
            prog_span,
            alias_span,
            logic_span,
        ),

        (Some((_, DefKind::Trait)), None) => {
            // trait method aliased by program function.
            // already checked the requirements at this point.
        }
        (Some((id1, DefKind::Trait)), Some((id2, DefKind::Trait))) => {
            if id1 != id2 {
                failwith(
                    tcx,
                    format!(
                        "A trait method can only be aliased by a logic method from the same trait. \
                            (program method defined in trait {}, logic alias defined in trait {})",
                        tcx.def_path_str(id1),
                        tcx.def_path_str(id2),
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }
        (Some((trait_id, DefKind::Trait)), Some((impl_id, DefKind::Impl { of_trait: false })))
        | (Some((impl_id, DefKind::Impl { of_trait: false })), Some((trait_id, DefKind::Trait))) => {
            // check that the type related to impl_id also implements trait trait_id
            if !impl_this_trait(ctx, impl_id, trait_id) {
                // If the logic function is in a trait and the program function in an impl,
                // this should be catched by the typechecker before we get here.
                // This is not true in the opposite case.
                let ty = tcx.type_of(impl_id).skip_binder();
                failwith(
                    tcx,
                    format!(
                        "Cannot use #[logic_alias] in this context, because \
                    type {ty:#?} does not implement trait {}.",
                        ctx.def_path_str(trait_id)
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }
        (Some((trait_id, DefKind::Trait)), Some((impl_id, DefKind::Impl { of_trait: true })))
        | (Some((impl_id, DefKind::Impl { of_trait: true })), Some((trait_id, DefKind::Trait))) => {
            // check that impl_id refers to an impl of the trait trait_id
            let tid = ctx.impl_trait_id(impl_id);
            let (lhs, rhs) = if prog_parent.map(|(_, kind)| matches!(kind, DefKind::Trait)).unwrap()
            {
                ("program function", "logic function")
            } else {
                ("logic function", "program function")
            };

            if tid != trait_id {
                failwith(
                    tcx,
                    format!(
                        //"Cross-trait aliasing is incorrect (trait {} and impl trait {})",
                        "Cannot use #[logic_alias] in this context, because \
                        {lhs} is defined in trait {}, and {rhs} is defined for trait {}.",
                        ctx.def_path_str(trait_id),
                        ctx.def_path_str(tid)
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }

        (Some((_, DefKind::Impl { .. })), None) => {
            // type impl or trait impl aliased by a program function.
            // already check the requirements at this point.
        }

        (
            Some((id1, DefKind::Impl { of_trait: false })),
            Some((id2, DefKind::Impl { of_trait: false })),
        ) => {
            // check that id1 and id2 refers to the same type
            let self_lhs = tcx.type_of(id1).instantiate_identity().skip_normalization();
            let self_rhs = tcx.type_of(id2).instantiate_identity().skip_normalization();

            if self_lhs != self_rhs {
                failwith(
                    tcx,
                    format!(
                        "Cannot use #[logic_alias] in this context, because \
                        program function is bound to type {self_lhs:#?} and logic function is bound to type {self_rhs:#?}"
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }

        (
            Some((impl_id, DefKind::Impl { of_trait: false })),
            Some((trait_impl_id, DefKind::Impl { of_trait: true })),
        )
        | (
            Some((trait_impl_id, DefKind::Impl { of_trait: true })),
            Some((impl_id, DefKind::Impl { of_trait: false })),
        ) => {
            // check that the impl_id and trait_impl_id have the same `Self` type
            let self_impl = tcx.type_of(impl_id).instantiate_identity().skip_normalization();
            let self_trait_impl =
                tcx.type_of(trait_impl_id).instantiate_identity().skip_normalization();

            if self_impl != self_trait_impl {
                let (lhs, rhs) = if prog_parent
                    .map(|(_, kind)| matches!(kind, DefKind::Impl { of_trait: false }))
                    .unwrap()
                {
                    ("program function", "logic function")
                } else {
                    ("logic function", "program function")
                };

                failwith(
                    tcx,
                    format!(
                        "Cannot #[logic_alias] in this context, because \
                        {lhs} is bound to type {self_impl:#?} and {rhs} is bound to type {self_trait_impl:#?}"
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }

        (
            Some((id1, DefKind::Impl { of_trait: true })),
            Some((id2, DefKind::Impl { of_trait: true })),
        ) => {
            if id1 != id2 {
                let t1 = ctx.def_path_str(ctx.impl_trait_id(id1));
                let t2 = ctx.def_path_str(ctx.impl_trait_id(id2));

                failwith(
                    tcx,
                    format!(
                        "Logic aliases between trait impl is incorrect \
                    (program function defined in impl {t1}, logic function defined in impl {t2})"
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }

        (_, _) => {
            // other cases are fine
        }
    }

    // only check this for functions
    if logic_parent.is_none() || prog_parent.is_none() {
        for arg in prog_subst
            .iter()
            .map(GenericArg::kind)
            .zip_longest(logic_subst.iter().map(GenericArg::kind))
        {
            use EitherOrBoth::*;

            match arg {
                Left(a) | Right(a) => {
                    let err = if arg.is_left() { "missing" } else { "additional" };

                    failwith(
                        tcx,
                        format!(
                            "mismatched generic parameters for #[logic_alias]: {err} parameter {a:?} in the alias"
                        ),
                        prog_span,
                        alias_span,
                        logic_span,
                    )
                }
                Both(GenericArgKind::Type(t1), GenericArgKind::Type(t2)) => {
                    if t1 != t2 {
                        failwith(
                            tcx,
                            format!("mismatched types in #[logic_alias]: expected {t1}, got {t2}"),
                            prog_span,
                            alias_span,
                            logic_span,
                        )
                    }
                }
                Both(GenericArgKind::Const(c1), GenericArgKind::Const(c2)) => {
                    let (pt, pname) = match c1.kind() {
                        rustc_type_ir::ConstKind::Param(p) => {
                            (p.find_const_ty_from_env(tcx.param_env(real_prog_id)), p.name)
                        }
                        _ => unreachable!(),
                    };

                    let (lt, lname) = match c2.kind() {
                        rustc_type_ir::ConstKind::Param(p) => {
                            (p.find_const_ty_from_env(tcx.param_env(real_logic_id)), p.name)
                        }
                        _ => unreachable!(),
                    };

                    if pt != lt || pname != lname {
                        failwith(
                            tcx,
                            format!(
                                "mismatched constants in #[logic_alias]: expected `{pname} : {pt}`, got `{lname} : {lt}`"
                            ),
                            prog_span,
                            alias_span,
                            logic_span,
                        )
                    }
                }
                Both(GenericArgKind::Lifetime(l1), GenericArgKind::Lifetime(l2)) => {
                    if l1 != l2 {
                        failwith(
                            tcx,
                            format!(
                                "mismatched lifetime parameters in #[logic_alias]: expected {l1}, got {l2}"
                            ),
                            prog_span,
                            alias_span,
                            logic_span,
                        )
                    }
                }
                Both(a1, a2) => failwith(
                    tcx,
                    format!(
                        "mismatched parameter kinds in #[logic_alias]: expected {a1:?}, got {a2:?}"
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                ),
            }
        }
    }
}
