//! Logic Function Aliases
//!
//! This module implements the core machinery for aliasing logic functions.
//!
//! # Definitions
//!
//! A logic alias can be of two kinds:
//! - a path to a logic function
//! - a call to a logic function
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
//! TODO: move this to user documentation
//! In this examples we have:
//! - The logic alias of `add_one` is `add_one_log`
//! - The alias closure of `add_one` is `result == add_one_log(x)`
//! - The prog_id of `add_one` is `add_one`
//! - The logic_id of `add_one` is `add_one_log`
//! - The closure_id of `add_one` is whatever DefId will be given the
//!   alias closure
//! - `add_two` #[ensures] clause contains one fake term
//!   `add_one(add_one(a))`
//! - `add_two` #[ensures] clause will be replaced by the aliased term
//!   `add_one_log(add_one_log(a))`
//! - `add_one` is an aliased function
//! - `add_one_log` is the alias function of `add_one`
//!
//!
//! # Compilation
//!
//! Logic aliases are compiled as follows:
//!
//! ## Step 1: preprocessing
//! During macro evaluation, every #[logic_alias] clause is replaced by an
//! #[ensures] clause of the form `result == <logic alias>`.
//! We also add an annotation `#[creusot::decl::logic_alias = <closure_id>]`
//! to retrieve the aliases later.
//! See [creusot-std-proc::creusot::specs::logic_alias]
//! and [creusot-std-proc::creusot::specs::ensures_inner]
//!
//! ## Step 2: alias loading
//! During the initialization of the `TranslationCtx`, we build a map
//! from the prog_id's to their associated closure_id's. We also check that the
//! aliases are valid (see below). Special care needs to be taken for aliases
//! located in `extern_spec!` blocks, as the aliased functions will be wrapped
//! by a local function. We therefore need to also bind the wrapper id to the
//! closure id.
//! See [creusot::ctx::load_logic_aliases]
//! and [creusot::logic_alias::check_validity]
//!
//! ## Step 3: substitution
//! See [creusot::translation::pearlite::from_thir::expr_term]
//! and [creusot::logic_alias::subst_call]
//!
//! # Validity of aliasing
//!
//! The following table shows the rules for aliasing:
//! (NB: This is still a work in progress, and I do not yet guarantee that `check_validity`
//!  enforces these rules properly, since they have been subject to quite some change
//!  recently following discussions with Diane and Li-Yao. I rather wait for a consensus
//!  on the Creusot team to apply any meaningfull changes to the current implementation).
//! +--------------------------------------------------------------------------------------------+
//! |   Program part    |    Logic part     |                    Validity                        |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  fun              |  fun              |  valid if both fun comes from the current crate,   |
//! |                   |                   |     or are located in an extern_spec!              |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  fun              |   trait           |    invalid                                         |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  fun              |   impl type       |    invalid                                         |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  fun              |   impl trait      |    invalid                                         |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  trait            |   fun             |    valid if `fun` comes from the current crate     |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  trait            |   trait           |    valid if in the same trait                      |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  trait            |   impl type       |    valid if `type` also implement `trait`  ?       |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  trait            |   impl trait      |    invalid                                         |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl type        |   fun             |    valid if `fun` comes from the current crate     |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl type        |   trait           |    valid if `type` implements `trait` and          |
//! |                   |                   |    logic function is sealed ?                      |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl type        |   impl type       |    valid if it's the same type (*)                 |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl type        |   impl trait      |    valid if it's the same type                     |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl trait       |   fun             |    valid if `fun` comes from the current crate     |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl trait       |   trait           |    valid if it's the same trait (**)               |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl trait       |   impl type       |    valid if `type` implements `trait`              |
//! |-------------------+-------------------+----------------------------------------------------|
//! |  impl trait       |   impl trait      |    valid if it's the same trait (**)               |
//! +-------------------+-------------------+----------------------------------------------------+
//!
//! (*) I'm not sure if this is really a big deal to have aliasing between methods from two
//! different types. Maybe we could to allow it as long as the signatures match?
//! (**) Do we really want this ? Do we want to go even further ?
//!

use crate::{
    ctx::TranslationCtx,
    translation::pearlite::{MapSubstitution, Scoped, Substable, Term, TermKind},
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, TypingEnv};
use rustc_span::Span;

fn get_ensures_body<'a, 'tcx>(
    ctx: &'a TranslationCtx<'tcx>,
    def_id: DefId,
) -> &'a Scoped<Term<'tcx>> {
    let def_id2 = ctx.extern_spec_items(def_id).unwrap_or(def_id);

    ctx.term(def_id2).expect("no ensures clause associated with this alias")
}

pub(crate) fn get_logic_id(ctx: &TranslationCtx, def_id: DefId) -> Option<DefId> {
    let ensures_body = get_ensures_body(ctx, def_id);

    if let TermKind::Binary { rhs, .. } = &ensures_body.1.kind {
        if let TermKind::Call { id, .. } = &rhs.kind { Some(*id) } else { None }
    } else {
        unreachable!("This should be an equality")
    }
}

pub(crate) fn pp_alias(ctx: &TranslationCtx, def_id: DefId, print_term: bool) -> String {
    let ensures_body = get_ensures_body(ctx, def_id);

    if let TermKind::Binary { rhs, .. } = &ensures_body.1.kind {
        if let TermKind::Call { id, .. } = &rhs.kind {
            ctx.def_path_str(*id)
        } else if print_term {
            format!("{rhs:#?}")
        } else {
            "<term>".into()
        }
    } else {
        "<none>".into()
    }
}

pub(crate) fn subst_call<'tcx, Args>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    alias_id: DefId,
    prog_subst: GenericArgsRef<'tcx>,
    prog_args: Args,
    prog_span: Span,
) -> Option<Term<'tcx>>
where
    Args: IntoIterator<Item = Term<'tcx>>,
{
    let ensures_body = get_ensures_body(ctx, alias_id);

    let mut args_subst = MapSubstitution::new();

    let prog_params = &ensures_body.0;
    for (param, term) in itertools::zip_eq(&prog_params[..prog_params.len() - 1], prog_args) {
        args_subst.insert(param.0, term.kind);
    }

    let helper_subst = |term: &Term<'tcx>| {
        let mut new_term = ctx.normalize_erasing_regions(
            typing_env,
            EarlyBinder::bind(ctx.tcx, term.clone()).instantiate(ctx.tcx, prog_subst),
        );
        new_term.subst(&args_subst);
        new_term
    };

    match &ensures_body.1.kind {
        TermKind::Binary { rhs, .. } => match &rhs.kind {
            TermKind::Call { id, args, subst: call_subst } => {
                let call_subst = ctx.normalize_erasing_regions(
                    typing_env,
                    EarlyBinder::bind(ctx.tcx, *call_subst).instantiate(ctx.tcx, prog_subst),
                );

                let res_args = args.iter().map(helper_subst);
                Some(Term::call_no_normalize(ctx.tcx, *id, call_subst, res_args).span(prog_span))
            }

            _ => Some(helper_subst(rhs)),
        },
        _ => unreachable!("this should be an equality"),
    }
}
