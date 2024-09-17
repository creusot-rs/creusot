use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    thir::{self, ClosureExpr, ExprKind, Thir},
    ty::{FnDef, TyCtxt, Visibility},
};
use rustc_span::Span;

use crate::{
    ctx::{parent_module, TranslationCtx},
    error::{Error, InternalError},
    pearlite::{pearlite_stub, Stub},
    specification::contract_of,
    translation::pearlite::{super_visit_term, TermKind, TermVisitor},
    util::{self, is_law, is_open_inv_result},
};

pub(crate) fn validate_trusted(ctx: &mut TranslationCtx) {
    for def_id in ctx.hir_crate_items(()).definitions() {
        let def_id = def_id.to_def_id();
        if util::get_builtin(ctx.tcx, def_id).is_some() && !util::is_trusted(ctx.tcx, def_id) {
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

        fn error(&self, id: DefId, span: Span) -> () {
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
    if util::is_spec(ctx.tcx, item) {
        return Some(());
    }

    // UGLY clone...
    let term = ctx.term(item)?.clone();

    if ctx.visibility(item) != Visibility::Restricted(parent_module(ctx.tcx, item))
        && util::opacity_witness_name(ctx.tcx, item).is_none()
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
    let def_path = tcx.def_path_str(def_id);

    def_path.ends_with("::ops::Mul::mul")
        || def_path.ends_with("::ops::Add::add")
        || def_path.ends_with("::ops::Sub::sub")
        || def_path.ends_with("::ops::Div::div")
        || def_path.ends_with("::ops::Rem::rem")
        || def_path.ends_with("::ops::Neg::neg")
        || def_path.ends_with("::boxed::Box::<T>::new")
        || def_path.ends_with("::ops::Deref::deref")
        || def_path.ends_with("::ops::DerefMut::deref_mut")
        || def_path.ends_with("Snapshot::<T>::from_fn")
}

pub(crate) fn validate_impls(ctx: &mut TranslationCtx) {
    for impl_id in ctx.all_local_trait_impls(()).values().flat_map(|i| i.iter()) {
        if !matches!(ctx.def_kind(*impl_id), DefKind::Impl { .. }) {
            continue;
        }
        use rustc_middle::ty::print::PrintTraitRefExt;
        let trait_ref = ctx.impl_trait_ref(*impl_id).unwrap().skip_binder();

        if util::is_trusted(ctx.tcx, trait_ref.def_id)
            != util::is_trusted(ctx.tcx, impl_id.to_def_id())
        {
            let msg = if util::is_trusted(ctx.tcx, trait_ref.def_id) {
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

            let item_type = util::item_type(ctx.tcx, impl_item);
            let trait_type = util::item_type(ctx.tcx, trait_item);
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
    pub(crate) fn of_def_id<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> Self {
        let is_snapshot = util::is_snapshot_closure(ctx.tcx, def_id);
        if util::is_predicate(ctx.tcx, def_id) && util::is_prophetic(ctx.tcx, def_id)
            || util::is_logic(ctx.tcx, def_id) && util::is_prophetic(ctx.tcx, def_id)
            || util::is_spec(ctx.tcx, def_id) && !is_snapshot
        {
            Purity::Logic { prophetic: true }
        } else if util::is_predicate(ctx.tcx, def_id)
            || util::is_logic(ctx.tcx, def_id)
            || is_snapshot
        {
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
            (Purity::Logic { prophetic: true }, Purity::Logic { prophetic: false }) => true,
            (
                Purity::Program { no_panic, terminates },
                Purity::Program { no_panic: no_panic2, terminates: terminates2 },
            ) => no_panic <= no_panic2 && terminates <= terminates2,
            (ctx, call) => ctx == call,
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

pub(crate) fn validate_purity(ctx: &mut TranslationCtx, def_id: LocalDefId) {
    let (thir, expr) = ctx
        .thir_body(def_id)
        .unwrap_or_else(|_| Error::from(InternalError("Cannot fetch THIR body")).emit(ctx.tcx));
    let thir = thir.borrow();
    if thir.exprs.is_empty() {
        Error::new(ctx.def_span(def_id), "type checking failed").emit(ctx.tcx);
    }

    let def_id = def_id.to_def_id();
    let purity = Purity::of_def_id(ctx, def_id);
    if matches!(purity, Purity::Program { .. }) && crate::util::is_no_translate(ctx.tcx, def_id) {
        return;
    }

    thir::visit::walk_expr(&mut PurityVisitor { ctx, thir: &thir, context: purity }, &thir[expr]);
}

pub(crate) struct PurityVisitor<'a, 'tcx> {
    pub(crate) ctx: &'a mut TranslationCtx<'tcx>,
    pub(crate) thir: &'a Thir<'tcx>,
    pub(crate) context: Purity,
}

impl<'a, 'tcx> PurityVisitor<'a, 'tcx> {
    fn purity(&mut self, fun: thir::ExprId, func_did: DefId) -> Purity {
        let stub = pearlite_stub(self.ctx.tcx, self.thir[fun].ty);

        if matches!(stub, Some(Stub::Fin))
            || util::is_predicate(self.ctx.tcx, func_did)
                && util::is_prophetic(self.ctx.tcx, func_did)
            || util::is_logic(self.ctx.tcx, func_did) && util::is_prophetic(self.ctx.tcx, func_did)
        {
            Purity::Logic { prophetic: true }
        } else if util::is_predicate(self.ctx.tcx, func_did)
            || util::is_logic(self.ctx.tcx, func_did)
            || util::get_builtin(self.ctx.tcx, func_did).is_some()
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
                // FIXME: like in detect_recursion (MIR visitor), we would need to specialize the trait functions.
                if let &FnDef(func_did, _) = self.thir[fun].ty.kind() {
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
                if util::is_spec(self.ctx.tcx, closure_id.into()) {
                    return;
                }

                let (thir, expr) = self.ctx.thir_body(closure_id).unwrap_or_else(|_| {
                    Error::from(InternalError("Cannot fetch THIR body")).emit(self.ctx.tcx)
                });
                let thir = thir.borrow();

                thir::visit::walk_expr(
                    &mut PurityVisitor { ctx: self.ctx, thir: &thir, context: self.context },
                    &thir[expr],
                );
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr)
    }
}
