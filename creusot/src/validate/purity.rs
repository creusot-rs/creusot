use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    thir::{self, ClosureExpr, ExprKind, Thir},
    ty::{FnDef, TypingEnv},
};

use crate::{
    contracts_items::{
        get_builtin, is_ghost_deref, is_ghost_deref_mut, is_ghost_into_inner, is_ghost_new,
        is_logic, is_no_translate, is_predicate, is_prophetic, is_snapshot_closure, is_spec,
    },
    ctx::TranslationCtx,
    error::CannotFetchThir,
    pearlite::{pearlite_stub, Stub},
    specification::contract_of,
    traits::TraitResolved,
};

use super::is_overloaded_item;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Purity {
    /// Same as `Program { terminates: true, no_panic: true }`, but can also call the few
    /// ghost-only functions (e.g. `GhostBox::new`).
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

    fn is_logic(self) -> bool {
        matches!(self, Self::Logic { .. })
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

pub(crate) fn validate_purity(
    ctx: &TranslationCtx,
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
    let typing_env = ctx.typing_env(def_id);

    let mut visitor =
        PurityVisitor { ctx, thir: &thir, context: purity, typing_env, thir_failed: false };
    thir::visit::walk_expr(&mut visitor, &thir[expr]);
    if visitor.thir_failed {
        Err(CannotFetchThir)
    } else {
        Ok(())
    }
}

struct PurityVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    thir: &'a Thir<'tcx>,
    context: Purity,
    /// Typing environment of the caller function
    typing_env: TypingEnv<'tcx>,
    // If `true`, we should error with a [`CannotFetchThir`] error.
    thir_failed: bool,
}

impl PurityVisitor<'_, '_> {
    fn purity(&self, fun: thir::ExprId, func_did: DefId) -> Purity {
        let tcx = self.ctx.tcx;
        let stub = pearlite_stub(tcx, self.thir[fun].ty);

        if matches!(stub, Some(Stub::Fin))
            || is_predicate(tcx, func_did) && is_prophetic(tcx, func_did)
            || is_logic(tcx, func_did) && is_prophetic(tcx, func_did)
        {
            Purity::Logic { prophetic: true }
        } else if is_predicate(tcx, func_did)
            || is_logic(tcx, func_did)
            || get_builtin(tcx, func_did).is_some()
            || stub.is_some()
        {
            Purity::Logic { prophetic: false }
        } else if is_ghost_into_inner(tcx, func_did)
            || is_ghost_new(tcx, func_did)
            || is_ghost_deref(tcx, func_did)
            || is_ghost_deref_mut(tcx, func_did)
        {
            Purity::Ghost
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
            ExprKind::Call { fun, ref args, .. } => {
                if let &FnDef(func_did, subst) = self.thir[fun].ty.kind() {
                    // try to specialize the called function if it is a trait method.
                    let subst = self.ctx.erase_regions(subst);
                    let func_did = if TraitResolved::is_trait_item(self.ctx.tcx, func_did) {
                        match TraitResolved::resolve_item(
                            self.ctx.tcx,
                            self.typing_env,
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
                    if !(self.context.can_call(fn_purity)
                        || fn_purity.is_logic() && is_overloaded_item(self.ctx.tcx, func_did))
                    {
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

                            let mut err = self.ctx.error(self.thir[fun].span, msg);
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
                                (Purity::Ghost, Purity::Program { .. }) => ("ghost", "non-pure"),
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
                } else if matches!(self.context, Purity::Logic { .. }) {
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
                    typing_env: self.typing_env,
                    thir_failed: false,
                };
                thir::visit::walk_expr(&mut visitor, &thir[expr]);
                if visitor.thir_failed {
                    self.thir_failed = true;
                    return;
                }
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
}
