//! Logic Function Aliases
//!
//! This module implements the core machinery for aliasing logic functions.
//!
//! # Definitions
//!
//! A logic alias can be of two kinds:
//! - a path to a logic function
//! - a pearlite term
//!
//! In both cases the logic alias must be a valid term.
//! Note that we do not allow the logic alias to be an arbitrary term,
//! as this would open the gates of hell on pearlite.
//!
//! Adding a `#[logic_alias]` clause on a function have two visible effects:
//! - An #[ensures] clause will automatically be added (see below)
//! - It becomes possible to use the prog_id in pearlite, as every fake term
//!   will be automatically replaced by an aliased term.
//!
//! # Example:
//! TODO: move this to user documentation
//!
//! ```
//! #[logic]
//! #[ensures(result == x + 1i64)]
//! fn add_one_log(x: i64) -> i64 { ... }
//!
//! #[logic_alias(add_one_log)]
//! fn add_one(x: i64) -> i64 { ... }
//!
//! #[ensures(result == add_one(add_one(a)))]
//! fn add_two(a: i64) -> i64 { ... }
//! ```
//! Roughly becomes:
//! ```
//! #[ensures(result == x + 1i64)]
//! fn add_one_log(x: i64) -> i64 { ... }
//!
//! #[ensures(result == add_one_log(x))]
//! fn add_one(x: i64) -> i64 { ... }
//!
//! #[ensures(result == add_one_log(add_one_log(a)))]
//! fn add_two(a: i64) -> bool { ... }
//! ```
//!

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
    if !ctx.is_aliased(prog_id) {
        return None;
    }

    let pre_sig = ctx.sig(prog_id);
    let Some(alias) = &pre_sig.contract.alias else {
        return None;
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
