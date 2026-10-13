// Logical Function Aliases
//
// ```
// #[logic]
// #[ensures(result == x + 1i64)]
// fn add_one_log(x: i64) -> i64 { ... }
//
// #[logic_alias(add_one_log)]
// fn add_one(x: i64) -> i64 { ... }
//
// #[ensures(result == add_one(add_one(a)))]
// fn add_two(a: i64) -> i64 { ... }
// ```
//
// Roughly becomes:
// ```
// #[ensures(result == x + 1i64)]
// fn add_one_log(x: i64) -> i64 { ... }
//
// #[ensures(result == add_one_log(x))]
// fn add_one(x: i64) -> i64 { ... }
//
// #[ensures(result == add_one_log(add_one_log(a)))]
// fn add_two(a: i64) -> bool { ... }
// ```
//

use crate::{
    ctx::TranslationCtx,
    translation::pearlite::{Substable, Term, TermKind},
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, TypingEnv};
use std::collections::HashMap;

pub(crate) fn get_logic_id(ctx: &TranslationCtx, def_id: DefId) -> Option<DefId> {
    let Some(alias) = &ctx.sig(def_id).contract.alias else {
        return None;
    };

    if let TermKind::Call { id, .. } = &alias.1.kind { Some(*id) } else { None }
}

pub(crate) fn subst_call<'tcx, Args>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    prog_id: DefId,
    prog_subst: GenericArgsRef<'tcx>,
    prog_args: Args,
) -> Option<Term<'tcx>>
where
    Args: IntoIterator<Item = Term<'tcx>>,
{
    // Beware: one could be tempted to remove the following test,
    // as the call to `ctx::sig` gives us the exact same information.
    // However this can cause infinite recursion, e.g:
    //      subst_call ->
    //      ctx.sig ->
    //      specification::pre_sig_of ->
    //      specification::contract_of ->
    //      ContractClauses::get_pre ->
    //      ctx.term ->
    //      pearlite::normalize ->
    //      subst_call ->
    //      <...>
    if !ctx.is_aliased(prog_id) {
        return None;
    }

    trace!("subst_call({prog_id:#?})");

    let pre_sig = ctx.sig(prog_id);
    let Some(alias) = &pre_sig.contract.alias else {
        unreachable!("ctx::is_aliased and ctx::sig disagree on the logic alias");
    };

    let mut args_subst = HashMap::new();
    for (param, term) in itertools::zip_eq(&pre_sig.inputs, prog_args) {
        args_subst.insert(param.0.0, term.kind);
    }

    let term = ctx.normalize_erasing_regions(
        typing_env,
        EarlyBinder::bind(ctx.tcx, alias.1.clone()).instantiate(ctx.tcx, prog_subst),
    );

    Some(term.subst(&args_subst).span(alias.0))
}
