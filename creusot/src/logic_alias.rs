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
