use crate::{
    backend::is_trusted_item,
    contracts_items::{
        Intrinsic, is_erasure, is_logic, is_prophetic, is_snapshot_closure, is_spec,
    },
    ctx::{HasTyCtxt, TranslationCtx},
    translation::traits::TraitResolved,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    thir::{self, ClosureExpr, ExprId, ExprKind, Thir, visit::Visitor},
    ty::{FnDef, TyCtxt, TypingEnv},
};
use rustc_span::sym;
use rustc_trait_selection::infer::InferCtxtExt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Purity {
    /// Same as `Program { terminates: true, ghost: true }`, but can also call the few
    /// ghost-only functions (e.g. `Ghost::new`).
    Ghost,
    Program {
        terminates: bool,
        ghost: bool,
    },
    Logic {
        prophetic: bool,
    },
}

impl Purity {
    pub(crate) fn of_def_id<'tcx>(ctx: &TranslationCtx<'tcx>, def_id: DefId) -> Self {
        if is_logic(ctx.tcx, def_id) {
            Purity::Logic { prophetic: is_prophetic(ctx.tcx, def_id) }
        } else if is_spec(ctx.tcx, def_id) {
            Purity::Logic { prophetic: !is_snapshot_closure(ctx.tcx, def_id) }
        } else {
            let contract = &ctx.sig(def_id).contract;
            Purity::Program { terminates: contract.check_terminates, ghost: contract.check_ghost }
        }
    }

    fn can_call(self, other: Purity) -> bool {
        match (self, other) {
            (Purity::Logic { prophetic }, Purity::Logic { prophetic: prophetic2 }) => {
                prophetic || !prophetic2
            }
            (
                Purity::Program { ghost, terminates },
                Purity::Program { ghost: ghost2, terminates: terminates2 },
            ) => ghost <= ghost2 && terminates <= terminates2,
            (Purity::Ghost, Purity::Ghost | Purity::Program { ghost: true, terminates: true }) => {
                true
            }
            (_, _) => false,
        }
    }

    fn as_str(&self) -> &'static str {
        match self {
            Purity::Ghost => "ghost",
            Purity::Program { terminates, ghost } => match (*terminates, *ghost) {
                (_, true) => "program (ghost)",
                (true, false) => "program (terminates)",
                (false, false) => "program",
            },
            Purity::Logic { prophetic: false } => "logic",
            Purity::Logic { prophetic: true } => "prophetic logic",
        }
    }
}

pub(crate) fn validate_purity<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    &(ref thir, expr): &(Thir<'tcx>, ExprId),
) {
    // Only start traversing from top-level definitions. Closures will be visited during the traversal
    // of their parents so that they can inherit the context from their parent.
    if ctx.tcx.is_closure_like(def_id) {
        return;
    }
    if !is_logic(ctx.tcx, def_id) && is_trusted_item(ctx.tcx, def_id) {
        return;
    }
    if let Some((span, alias_id)) = ctx.logical_alias(def_id) {
        if is_logic(ctx.tcx, def_id) {
            ctx.dcx()
                .struct_span_err(
                    ctx.def_ident_span(def_id).unwrap_or_default(),
                    "Only program functions can use `#[has_logical_alias(...)]`",
                )
                .with_span_label(span, "alias defined here")
                .emit();
        }
        if !is_logic(ctx.tcx, alias_id) {
            ctx.dcx()
                .struct_span_err(span, "Only logic functions can be aliased")
                .with_note(format!("{} is not a logic function", ctx.def_path_str(alias_id)))
                .emit();
        }
    }

    let typing_env = ctx.typing_env(def_id);
    PurityVisitor { ctx, thir, context: Purity::of_def_id(ctx, def_id), typing_env }
        .visit_expr(&thir[expr]);
}

struct PurityVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    thir: &'a Thir<'tcx>,
    context: Purity,
    /// Typing environment of the caller function
    typing_env: TypingEnv<'tcx>,
}

enum ClosureKind {
    Spec(LocalDefId),
    Erasure,
}

impl PurityVisitor<'_, '_> {
    fn purity(&self, func_did: DefId, args: &[ExprId]) -> Purity {
        if is_logic(self.ctx.tcx, func_did) {
            Purity::Logic { prophetic: is_prophetic(self.ctx.tcx, func_did) }
        } else if let Intrinsic::GhostIntoInner
        | Intrinsic::GhostNew
        | Intrinsic::GhostDeref
        | Intrinsic::GhostDerefMut = self.ctx.intrinsic(func_did)
        {
            Purity::Ghost
        } else {
            let contract = &self.ctx.sig(func_did).contract;
            let is_ghost = self.implements_fn_ghost(func_did, args);
            let terminates = contract.check_terminates || is_ghost;
            let ghost = contract.check_ghost || is_ghost;
            Purity::Program { terminates, ghost }
        }
    }

    /// Returns `true` if `func_did` is one of `call`, `call_mut` or `call_once`, and
    /// the closure being called implements `FnGhost`.
    fn implements_fn_ghost(&self, func_did: DefId, args: &[ExprId]) -> bool {
        let Some(trait_did) = self.ctx.trait_of_assoc(func_did) else { return false };
        if !self.ctx.is_fn_trait(trait_did) {
            return false;
        };
        let ty = self.thir[args[0]].ty.peel_refs();
        let (infcx, param_env) = self.ctx.infer_ctxt().build_with_typing_env(self.typing_env);
        infcx
            .type_implements_trait(Intrinsic::FnGhost.get(self.ctx), [ty], param_env)
            .must_apply_considering_regions()
    }

    /// If the expression is a closure with attribute `creusot::spec`, return `Some` of its `LocalDefId`, otherwise `None`.
    fn get_spec_closure(&self, mut expr: ExprId) -> Option<ClosureKind> {
        loop {
            match self.thir[expr].kind {
                ExprKind::Scope { value, .. } => expr = value,
                ExprKind::Block { block } => {
                    let block = &self.thir[block];
                    if !block.stmts.is_empty() {
                        return None;
                    }
                    let Some(expr_) = block.expr else { return None };
                    expr = expr_;
                }
                ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                    if is_spec(self.ctx.tcx, closure_id.to_def_id()) {
                        return Some(ClosureKind::Spec(closure_id));
                    } else if is_erasure(self.ctx.tcx, closure_id.to_def_id()) {
                        return Some(ClosureKind::Erasure);
                    }
                    return None;
                }
                _ => return None,
            }
        }
    }

    /// Validate the body of a spec closure.
    fn validate_spec_purity(&mut self, closure_id: LocalDefId, prophetic: bool) {
        // If this is None there must be a type error that will be reported later so we can skip this silently.
        let Some((thir, expr)) = self.ctx.get_local_thir(closure_id) else { return };
        PurityVisitor { thir, context: Purity::Logic { prophetic }, ..*self }
            .visit_expr(&thir[*expr]);
    }

    /// Return `false` if this is not a `creusot::spec` or `creusot::erasure` closure.
    fn try_visit_spec_stmt(&mut self, stmt: &thir::Stmt) -> bool {
        let thir::StmtKind::Let { ref pattern, initializer: Some(init), else_block, span, .. } =
            stmt.kind
        else {
            return false;
        };
        match self.get_spec_closure(init) {
            Some(ClosureKind::Spec(closure_id)) => {
                // If the statement is a spec statement, visit it.
                let thir::PatKind::Wild = pattern.kind else {
                    self.ctx
                        .dcx()
                        .span_fatal(pattern.span, "expected a wildcard pattern in spec statement")
                };
                if else_block.is_some() {
                    self.ctx.dcx().span_fatal(span, "expected no else block in spec statement")
                };
                self.validate_spec_purity(closure_id, true);
                true
            }
            Some(ClosureKind::Erasure) => true,
            None => false,
        }
    }
}

impl<'a, 'tcx> Visitor<'a, 'tcx> for PurityVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a thir::Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call { fun, ref args, .. } => {
                if let &FnDef(func_did, subst) = self.thir[fun].ty.kind() {
                    // try to specialize the called function if it is a trait method.
                    let subst = self.ctx.erase_and_anonymize_regions(subst);
                    let (func_did, _) =
                        TraitResolved::resolve_item(self.ctx.tcx, self.typing_env, func_did, subst)
                            .to_opt(func_did, subst)
                            .unwrap();

                    let fn_purity = self.purity(func_did, args);
                    let fn_purity = match self.ctx.logical_alias(func_did) {
                        Some((_, alias_did)) if !self.context.can_call(fn_purity) => {
                            self.purity(alias_did, args)
                        }
                        _ => fn_purity,
                    };
                    if matches!(self.context, Purity::Logic { .. })
                        && (
                            // These methods are allowed to cheat the purity restrictions
                            self.ctx.is_diagnostic_item(sym::box_new, func_did)
                                || matches!(
                                    self.ctx.intrinsic(func_did),
                                    Intrinsic::GhostDeref | Intrinsic::GhostDerefMut
                                )
                        )
                    {
                    } else if !self.context.can_call(fn_purity) {
                        // Emit a nicer error specifically for calls of ghost functions.
                        if fn_purity == Purity::Ghost
                            && matches!(self.context, Purity::Program { .. })
                        {
                            match self.ctx.intrinsic(func_did) {
                                Intrinsic::GhostIntoInner => self
                                    .error(expr.span, "trying to access the contents of a ghost variable in program context").emit(),
                                Intrinsic::GhostDeref | Intrinsic::GhostDerefMut => self
                                    .error(expr.span, "dereference of a ghost variable in program context").emit(),
                                Intrinsic::GhostNew => self
                                    .error(
                                        expr.span,
                                        "cannot create a ghost variable in program context",
                                    )
                                    .with_span_suggestion(
                                        expr.span,
                                        "try wrapping this expression in `ghost!` instead",
                                        format!(
                                            "ghost!({})",
                                            self.ctx
                                                .sess
                                                .source_map()
                                                .span_to_snippet(self.thir.exprs[args[0]].span)
                                                .unwrap()
                                        ),
                                        rustc_errors::Applicability::MachineApplicable,
                                    )
                                    .emit(),
                                _ => unreachable!(),
                            };
                        } else {
                            let (caller, callee) = match (self.context, fn_purity) {
                                (Purity::Program { .. } | Purity::Ghost, Purity::Logic { .. }) => {
                                    ("program", "logic")
                                }
                                (Purity::Ghost, Purity::Program { .. }) => ("ghost", "non-ghost"),
                                (Purity::Logic { .. }, Purity::Program { .. } | Purity::Ghost) => {
                                    ("logic", "program")
                                }
                                _ => (self.context.as_str(), fn_purity.as_str()),
                            };
                            let msg = format!(
                                "called {callee} function `{}` in {caller} context",
                                self.ctx.def_path_str(func_did),
                            );

                            self.ctx.dcx().span_err(self.thir[fun].span, msg);
                        }
                    }
                    if Intrinsic::SnapshotFromFn.is(self.ctx, func_did) {
                        assert!(args.len() == 1);
                        let Some(ClosureKind::Spec(closure_id)) = self.get_spec_closure(args[0])
                        else {
                            self.ctx.dcx().span_fatal(
                                expr.span,
                                "expected a spec closure as argument to `snapshot_from_fn`",
                            );
                        };
                        self.validate_spec_purity(closure_id, false);
                        return;
                    }
                } else if matches!(self.context, Purity::Logic { .. }) {
                    // TODO Add a "code" back in
                    self.ctx.dcx().span_fatal(expr.span, "non function call in logical context")
                }
            }
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                if is_spec(self.ctx.tcx, closure_id.into()) {
                    self.ctx.dcx().span_fatal(
                        expr.span,
                        format!("unexpected spec closure {}", self.ctx.def_path_str(closure_id)),
                    );
                }
                // If this is None there must be a type error that will be reported later so we can skip this silently.
                let Some((thir, expr)) = self.ctx.get_local_thir(closure_id) else { return };
                PurityVisitor { thir, ..*self }.visit_expr(&thir[*expr]);
            }
            ExprKind::Scope {
                region_scope: _,
                lint_level: thir::LintLevel::Explicit(hir_id),
                value: _,
            } => {
                if super::is_ghost_block(self.ctx.tcx, hir_id) {
                    let old_context = std::mem::replace(&mut self.context, Purity::Ghost);
                    thir::visit::walk_expr(self, expr);
                    self.context = old_context;
                    return;
                }
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr)
    }

    fn visit_stmt(&mut self, stmt: &'a thir::Stmt<'tcx>) {
        if !self.try_visit_spec_stmt(stmt) {
            thir::visit::walk_stmt(self, stmt)
        }
    }
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for PurityVisitor<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}
