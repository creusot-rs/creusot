use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    thir::{self, ClosureExpr, ExprKind, Thir},
    ty::{FnDef, ParamEnv, TyCtxt, Visibility},
};
use rustc_span::Span;

use crate::{
    contracts_items::{
        get_builtin, is_ghost_deref, is_ghost_deref_mut, is_law, is_logic, is_no_translate,
        is_open_inv_result, is_predicate, is_prophetic, is_snapshot_closure, is_snapshot_deref,
        is_spec, is_trusted, opacity_witness_name,
    },
    ctx::TranslationCtx,
    error::CannotFetchThir,
    pearlite::{pearlite_stub, Stub},
    specification::contract_of,
    traits::TraitResolved,
    translation::pearlite::{super_visit_term, TermKind, TermVisitor},
    util::parent_module,
};

pub(crate) fn validate_trusted(ctx: &mut TranslationCtx) {
    for def_id in ctx.hir_crate_items(()).definitions() {
        let def_id = def_id.to_def_id();
        if get_builtin(ctx.tcx, def_id).is_some() && !is_trusted(ctx.tcx, def_id) {
            ctx.error(
                ctx.def_span(def_id),
                "Builtin declarations should be annotated with #[trusted].",
            )
            .emit();
        }
    }
}

pub(crate) fn validate_opacity(ctx: &mut TranslationCtx, item: DefId) -> Option<()> {
    struct OpacityVisitor<'a, 'tcx> {
        ctx: &'a TranslationCtx<'tcx>,
        opacity: Option<DefId>,
        source_item: DefId,
    }

    impl<'a, 'tcx> OpacityVisitor<'a, 'tcx> {
        fn is_visible_enough(&self, id: DefId) -> bool {
            match self.opacity {
                None => self.ctx.visibility(id) == Visibility::Public,
                Some(opa) => self.ctx.visibility(id).is_accessible_from(opa, self.ctx.tcx),
            }
        }

        fn error(&self, id: DefId, span: Span) {
            self.ctx.error(
                span,
                &format!(
                    "Cannot make `{:?}` transparent in `{:?}` as it would call a less-visible item.",
                    self.ctx.def_path_str(id), self.ctx.def_path_str(self.source_item)
                ),
            ).emit();
        }
    }

    impl<'a, 'tcx> TermVisitor<'tcx> for OpacityVisitor<'a, 'tcx> {
        fn visit_term(&mut self, term: &crate::translation::pearlite::Term<'tcx>) {
            match &term.kind {
                TermKind::Item(id, _) => {
                    if !self.is_visible_enough(*id) {
                        self.error(*id, term.span)
                    }
                }
                TermKind::Call { id, .. } => {
                    if !self.is_visible_enough(*id) {
                        self.error(*id, term.span)
                    }
                }
                TermKind::Constructor { typ, .. } => {
                    if !self.is_visible_enough(*typ) {
                        self.error(*typ, term.span)
                    }
                }
                _ => super_visit_term(term, self),
            }
        }
    }

    if is_spec(ctx.tcx, item) {
        return Some(());
    }

    // UGLY clone...
    let term = ctx.term(item)?.clone();

    if ctx.visibility(item) != Visibility::Restricted(parent_module(ctx.tcx, item))
        && opacity_witness_name(ctx.tcx, item).is_none()
    {
        ctx.error(ctx.def_span(item), "Non private definitions must have an explicit transparency. Please add #[open(..)] to your definition").emit();
    }

    let opacity = ctx.opacity(item).scope();
    OpacityVisitor { opacity, ctx, source_item: item }.visit_term(&term);
    Some(())
}

// Validate that laws have no additional generic parameters.
// This is because laws are auto-loaded, and we do not want to generate polymorphic WhyML code
pub(crate) fn validate_traits(ctx: &mut TranslationCtx) {
    let mut law_violations = Vec::new();

    for trait_item_id in ctx.hir_crate_items(()).trait_items() {
        let trait_item = ctx.hir().trait_item(trait_item_id);

        if is_law(ctx.tcx, trait_item.owner_id.def_id.to_def_id())
            && !ctx.generics_of(trait_item.owner_id.def_id).own_params.is_empty()
        {
            law_violations.push((trait_item.owner_id.def_id, trait_item.span))
        }
    }

    for (_, sp) in law_violations {
        ctx.error(sp, "Laws cannot have additional generic parameters").emit();
    }
}

// These methods are allowed to cheat the purity restrictions because they are lang items we cannot redefine
fn is_overloaded_item(tcx: TyCtxt, def_id: DefId) -> bool {
    if let Some(name) = tcx.get_diagnostic_name(def_id) {
        match name.as_str() {
            "box_new" | "deref_method" | "deref_mut_method" => true,
            _ => {
                is_snapshot_deref(tcx, def_id)
                    || is_ghost_deref(tcx, def_id)
                    || is_ghost_deref_mut(tcx, def_id)
            }
        }
    } else {
        false
    }
}

pub(crate) fn validate_impls(ctx: &mut TranslationCtx) {
    for impl_id in ctx.all_local_trait_impls(()).values().flat_map(|i| i.iter()) {
        if !matches!(ctx.def_kind(*impl_id), DefKind::Impl { .. }) {
            continue;
        }
        use rustc_middle::ty::print::PrintTraitRefExt;
        let trait_ref = ctx.impl_trait_ref(*impl_id).unwrap().skip_binder();

        if is_trusted(ctx.tcx, trait_ref.def_id) != is_trusted(ctx.tcx, impl_id.to_def_id()) {
            let msg = if is_trusted(ctx.tcx, trait_ref.def_id) {
                format!(
                    "Expected implementation of trait `{}` for `{}` to be marked as `#[trusted]`",
                    trait_ref.print_only_trait_path(),
                    trait_ref.self_ty()
                )
            } else {
                format!(
                    "Cannot have trusted implementation of untrusted trait `{}`",
                    trait_ref.print_only_trait_path()
                )
            };
            ctx.error(ctx.def_span(impl_id.to_def_id()), &msg).emit();
        }

        let implementors = ctx.impl_item_implementor_ids(impl_id.to_def_id());

        let implementors =
            ctx.with_stable_hashing_context(|hcx| implementors.to_sorted(&hcx, true));
        for (&trait_item, &impl_item) in implementors {
            if let Some(open_inv_trait) = ctx.params_open_inv(trait_item) {
                let open_inv_impl = ctx.params_open_inv(impl_item).unwrap();
                for &i in open_inv_trait {
                    if !open_inv_impl.contains(&i) {
                        let name_param = ctx.fn_arg_names(impl_item)[i];
                        ctx.error(
                            ctx.def_span(impl_item),
                            &format!(
                                "Parameter `{name_param}` has the `#[creusot::open_inv]` attribute in the trait declaration, but not in the implementation."
                            ),
                        ).emit();
                    }
                }
            }

            if is_open_inv_result(ctx.tcx, impl_item) && !is_open_inv_result(ctx.tcx, trait_item) {
                ctx.error(
                    ctx.def_span(impl_item),
                    &format!(
                        "Function `{}` should not have the `#[open_inv_result]` attribute, as specified by the trait declaration",
                        ctx.item_name(impl_item),
                    ),
                ).emit();
            }

            if is_overloaded_item(ctx.tcx, trait_item) {
                continue;
            };

            let item_type = ctx.item_type(impl_item);
            let trait_type = ctx.item_type(trait_item);
            if !item_type.can_implement(trait_type) {
                ctx.error(
                    ctx.def_span(impl_item),
                    &format!(
                        "Expected `{}` to be a {} as specified by the trait declaration",
                        ctx.item_name(impl_item),
                        trait_type.to_str()
                    ),
                )
                .emit();
            } else {
                let item_contract = crate::specification::contract_of(ctx, impl_item);
                let trait_contract = crate::specification::contract_of(ctx, trait_item);
                if trait_contract.no_panic && !item_contract.no_panic {
                    ctx.error(
                        ctx.def_span(impl_item),
                        &format!(
                            "Expected `{}` to be `#[pure]` as specified by the trait declaration",
                            ctx.item_name(impl_item),
                        ),
                    )
                    .emit();
                } else if trait_contract.terminates && !item_contract.terminates {
                    ctx.error(
                        ctx.def_span(impl_item),
                        &format!(
                            "Expected `{}` to be `#[terminates]` as specified by the trait declaration",
                            ctx.item_name(impl_item),
                        ),
                    )
                    .emit();
                }
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Purity {
    Program { terminates: bool, no_panic: bool },
    Logic { prophetic: bool },
}

impl Purity {
    pub(crate) fn of_def_id(ctx: &mut TranslationCtx, def_id: DefId) -> Self {
        let is_snapshot = is_snapshot_closure(ctx.tcx, def_id);
        if is_predicate(ctx.tcx, def_id) && is_prophetic(ctx.tcx, def_id)
            || is_logic(ctx.tcx, def_id) && is_prophetic(ctx.tcx, def_id)
            || is_spec(ctx.tcx, def_id) && !is_snapshot
        {
            Purity::Logic { prophetic: true }
        } else if is_predicate(ctx.tcx, def_id) || is_logic(ctx.tcx, def_id) || is_snapshot {
            Purity::Logic { prophetic: false }
        } else {
            let contract = contract_of(ctx, def_id);
            let terminates = contract.terminates;
            let no_panic = contract.no_panic;
            Purity::Program { terminates, no_panic }
        }
    }

    fn can_call(self, other: Purity) -> bool {
        match (self, other) {
            (Purity::Logic { prophetic }, Purity::Logic { prophetic: prophetic2 }) => {
                prophetic || !prophetic2
            }
            (
                Purity::Program { no_panic, terminates },
                Purity::Program { no_panic: no_panic2, terminates: terminates2 },
            ) => no_panic <= no_panic2 && terminates <= terminates2,
            (_, _) => false,
        }
    }

    fn as_str(&self) -> &'static str {
        match self {
            Purity::Program { terminates, no_panic } => match (*terminates, *no_panic) {
                (true, true) => "program (pure)",
                (true, false) => "program (terminates)",
                (false, true) => "program (no panic)",
                (false, false) => "program",
            },
            Purity::Logic { prophetic: false } => "logic",
            Purity::Logic { prophetic: true } => "prophetic logic",
        }
    }
}

pub(crate) fn validate_purity(
    ctx: &mut TranslationCtx,
    def_id: LocalDefId,
) -> Result<(), CannotFetchThir> {
    let (thir, expr) = ctx.fetch_thir(def_id)?;
    let thir = thir.borrow();
    if thir.exprs.is_empty() {
        // TODO: put this inside `fetch_thir`?
        return Err(CannotFetchThir);
    }

    let def_id = def_id.to_def_id();
    let purity = Purity::of_def_id(ctx, def_id);
    if matches!(purity, Purity::Program { .. }) && is_no_translate(ctx.tcx, def_id) {
        return Ok(());
    }
    let param_env = ctx.tcx.param_env(def_id);

    let mut visitor =
        PurityVisitor { ctx, thir: &thir, context: purity, param_env, thir_failed: false };
    thir::visit::walk_expr(&mut visitor, &thir[expr]);
    if visitor.thir_failed {
        Err(CannotFetchThir)
    } else {
        Ok(())
    }
}

struct PurityVisitor<'a, 'tcx> {
    ctx: &'a mut TranslationCtx<'tcx>,
    thir: &'a Thir<'tcx>,
    context: Purity,
    /// Typing environment of the caller function
    param_env: ParamEnv<'tcx>,
    // If `true`, we should error with a [`CannotFetchThir`] error.
    thir_failed: bool,
}

impl<'a, 'tcx> PurityVisitor<'a, 'tcx> {
    fn purity(&mut self, fun: thir::ExprId, func_did: DefId) -> Purity {
        let stub = pearlite_stub(self.ctx.tcx, self.thir[fun].ty);

        if matches!(stub, Some(Stub::Fin))
            || is_predicate(self.ctx.tcx, func_did) && is_prophetic(self.ctx.tcx, func_did)
            || is_logic(self.ctx.tcx, func_did) && is_prophetic(self.ctx.tcx, func_did)
        {
            Purity::Logic { prophetic: true }
        } else if is_predicate(self.ctx.tcx, func_did)
            || is_logic(self.ctx.tcx, func_did)
            || get_builtin(self.ctx.tcx, func_did).is_some()
            || stub.is_some()
        {
            Purity::Logic { prophetic: false }
        } else {
            let contract = contract_of(self.ctx, func_did);
            let terminates = contract.terminates;
            let no_panic = contract.no_panic;
            Purity::Program { terminates, no_panic }
        }
    }
}

impl<'a, 'tcx> thir::visit::Visitor<'a, 'tcx> for PurityVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a thir::Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call { fun, .. } => {
                if let &FnDef(func_did, subst) = self.thir[fun].ty.kind() {
                    // try to specialize the called function if it is a trait method.
                    let subst = self.ctx.erase_regions(subst);
                    let func_did = if TraitResolved::is_trait_item(self.ctx.tcx, func_did) {
                        match TraitResolved::resolve_item(
                            self.ctx.tcx,
                            self.param_env,
                            func_did,
                            subst,
                        ) {
                            TraitResolved::Instance(id, _) => id,
                            _ => func_did,
                        }
                    } else {
                        func_did
                    };

                    let fn_purity = self.purity(fun, func_did);
                    if !self.context.can_call(fn_purity)
                        && !is_overloaded_item(self.ctx.tcx, func_did)
                    {
                        let (caller, callee) = match (self.context, fn_purity) {
                            (Purity::Program { .. }, Purity::Program { .. })
                            | (Purity::Logic { .. }, Purity::Logic { .. }) => {
                                (self.context.as_str(), fn_purity.as_str())
                            }
                            (Purity::Program { .. }, Purity::Logic { .. }) => ("program", "logic"),
                            (Purity::Logic { .. }, Purity::Program { .. }) => ("logic", "program"),
                        };
                        let msg = format!(
                            "called {callee} function `{}` in {caller} context",
                            self.ctx.def_path_str(func_did),
                        );

                        self.ctx.dcx().span_err(self.thir[fun].span, msg);
                    }
                } else if !matches!(self.context, Purity::Program { .. }) {
                    // TODO Add a "code" back in
                    self.ctx.dcx().span_fatal(expr.span, "non function call in logical context")
                }
            }
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                if is_spec(self.ctx.tcx, closure_id.into()) {
                    return;
                }

                let Ok((thir, expr)) = self.ctx.thir_body(closure_id) else {
                    self.thir_failed = true;
                    return;
                };
                let thir = thir.borrow();

                let mut visitor = PurityVisitor {
                    ctx: self.ctx,
                    thir: &thir,
                    context: self.context,
                    param_env: self.param_env,
                    thir_failed: false,
                };
                thir::visit::walk_expr(&mut visitor, &thir[expr]);
                if visitor.thir_failed {
                    self.thir_failed = true;
                    return;
                }
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr)
    }
}
