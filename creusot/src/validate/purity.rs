use crate::{
    backend::is_trusted_item,
    contracts_items::{
        get_fn_ghost_trait, is_box_new, is_ghost_deref, is_ghost_deref_mut, is_ghost_into_inner,
        is_ghost_new, is_logic, is_prophetic, is_snap_from_fn, is_snapshot_closure, is_spec,
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
use rustc_trait_selection::infer::InferCtxtExt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Purity {
    /// Same as `Program { terminates: true, no_panic: true }`, but can also call the few
    /// ghost-only functions (e.g. `Ghost::new`).
    Ghost,
    Program {
        terminates: bool,
        no_panic: bool,
    },
    Logic {
        prophetic: bool,
    },
}

impl Purity {
    pub(crate) fn of_def_id(ctx: &TranslationCtx, def_id: DefId) -> Self {
        if is_logic(ctx.tcx, def_id) {
            Purity::Logic { prophetic: is_prophetic(ctx.tcx, def_id) }
        } else if is_spec(ctx.tcx, def_id) {
            Purity::Logic { prophetic: !is_snapshot_closure(ctx.tcx, def_id) }
        } else {
            let contract = &ctx.sig(def_id).contract;
            Purity::Program { terminates: contract.terminates, no_panic: contract.no_panic }
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
            (
                Purity::Ghost,
                Purity::Ghost | Purity::Program { no_panic: true, terminates: true },
            ) => true,
            (_, _) => false,
        }
    }

    fn as_str(&self) -> &'static str {
        match self {
            Purity::Ghost => "ghost",
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

pub(crate) fn validate_purity<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    &(ref thir, expr): &(Thir<'tcx>, ExprId),
) {
    // Only start traversing from top-level definitions. Closures will be visited during the traversal
    // of their parents so that they can inherit the context from their parent.
    if ctx.tcx.is_closure_like(def_id) || is_trusted_item(ctx.tcx, def_id) {
        return;
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

impl PurityVisitor<'_, '_> {
    fn purity(&self, func_did: DefId, args: &[ExprId]) -> Purity {
        if is_logic(self.ctx.tcx, func_did) {
            Purity::Logic { prophetic: is_prophetic(self.ctx.tcx, func_did) }
        } else if is_ghost_into_inner(self.ctx.tcx, func_did)
            || is_ghost_new(self.ctx.tcx, func_did)
            || is_ghost_deref(self.ctx.tcx, func_did)
            || is_ghost_deref_mut(self.ctx.tcx, func_did)
        {
            Purity::Ghost
        } else {
            let contract = &self.ctx.sig(func_did).contract;
            let is_ghost = self.implements_fn_ghost(func_did, args);
            let terminates = contract.terminates || is_ghost;
            let no_panic = contract.no_panic || is_ghost;
            Purity::Program { terminates, no_panic }
        }
    }

    /// Returns `true` if `func_did` is one of `call`, `call_mut` or `call_once`, and
    /// the closure being called implements `FnGhost`.
    fn implements_fn_ghost(&self, func_did: DefId, args: &[ExprId]) -> bool {
        let tcx = self.ctx.tcx;
        let Some(trait_did) = tcx.trait_of_assoc(func_did) else { return false };
        if !tcx.is_fn_trait(trait_did) {
            return false;
        };
        let ty = self.thir[args[0]].ty.peel_refs();
        let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(self.typing_env);
        let res = infcx.type_implements_trait(get_fn_ghost_trait(tcx), [ty], param_env);
        res.must_apply_considering_regions()
    }

    /// If the expression is a closure with attribute `creusot::spec`, return `Some` of its `LocalDefId`, otherwise `None`.
    fn get_spec_closure(&self, mut expr: ExprId) -> Option<LocalDefId> {
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
                        return Some(closure_id);
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
        }
    }

    /// Validate the body of a spec closure.
    fn validate_spec_purity(&mut self, closure_id: LocalDefId, prophetic: bool) {
        // If this is None there must be a type error that will be reported later so we can skip this silently.
        let Some((thir, expr)) = self.ctx.get_thir(closure_id) else { return };
        PurityVisitor { thir, context: Purity::Logic { prophetic }, ..*self }
            .visit_expr(&thir[expr]);
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
                    let subst = self.ctx.erase_regions(subst);
                    let (func_did, _) =
                        TraitResolved::resolve_item(self.ctx.tcx, self.typing_env, func_did, subst)
                            .to_opt(func_did, subst)
                            .unwrap();

                    let fn_purity = self.purity(func_did, args);
                    if matches!(self.context, Purity::Logic { .. })
                        && (
                            // These methods are allowed to cheat the purity restrictions
                            is_box_new(self.ctx.tcx, func_did)
                                || is_ghost_deref(self.ctx.tcx, func_did)
                                || is_ghost_deref_mut(self.ctx.tcx, func_did)
                        )
                    {
                    } else if !self.context.can_call(fn_purity) {
                        // Emit a nicer error specifically for calls of ghost functions.
                        if fn_purity == Purity::Ghost
                            && matches!(self.context, Purity::Program { .. })
                        {
                            let tcx = self.ctx.tcx;
                            let msg = if is_ghost_into_inner(tcx, func_did) {
                                "trying to access the contents of a ghost variable in program context"
                            } else if is_ghost_deref(tcx, func_did)
                                || is_ghost_deref_mut(tcx, func_did)
                            {
                                "dereference of a ghost variable in program context"
                            } else {
                                "cannot create a ghost variable in program context"
                            };

                            let mut err = self.error(expr.span, msg);
                            if is_ghost_new(tcx, func_did) {
                                err = err.with_span_suggestion(
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
                                );
                            }
                            err.emit();
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
                    if is_snap_from_fn(self.ctx.tcx, func_did) {
                        assert!(args.len() == 1);
                        let Some(closure_id) = self.get_spec_closure(args[0]) else {
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
                let Some((ref thir, expr)) = self.ctx.get_thir(closure_id) else { return };
                PurityVisitor { thir, ..*self }.visit_expr(&thir[expr]);
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
        if let thir::StmtKind::Let {
            ref pattern, initializer: Some(init), else_block, span, ..
        } = stmt.kind
            && let Some(closure_id) = self.get_spec_closure(init)
        {
            // If the statement is a spec statement, visit it.
            let thir::PatKind::Wild = pattern.kind else {
                self.ctx
                    .dcx()
                    .span_fatal(pattern.span, "expected a wildcard pattern in spec statement")
            };
            if else_block.is_some() {
                self.ctx.dcx().span_fatal(span, "expected no else block in spec statement")
            };
            self.validate_spec_purity(closure_id, true)
        } else {
            thir::visit::walk_stmt(self, stmt)
        }
    }
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for PurityVisitor<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}
