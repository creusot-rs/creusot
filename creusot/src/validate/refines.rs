use std::collections::HashMap;

use rustc_hir::{HirId, def_id::DefId};
use rustc_middle::{thir::{self, BlockId, ExprId, ExprKind, PatKind, StmtId, Thir}, ty::TyCtxt};
use rustc_span::Span;

use crate::{
    contracts_items::{is_refines, is_spec}, ctx::{HasTyCtxt as _, TranslationCtx}, validate::ghost::is_ghost_ty_
};

pub(crate) fn validate_refines(ctx: &TranslationCtx) {
    for (left, right) in ctx.refines.iter() {
        for refined in right {
            check_refines(ctx, *left, *refined);
        }
    }
}

fn check_refines(ctx: &TranslationCtx, left: DefId, right: DefId) {
    let left_local = left.as_local().unwrap_or_else(|| {
        ctx.crash_and_error(ctx.def_span(left), "Refining function must be local")
    });
    let right_local = right.as_local().unwrap_or_else(|| {
        ctx.crash_and_error(
            ctx.def_span(right),
            "Refined function must be local (refining extern functions is not implemented)",
        )
    });
    let left_thir = ctx.thir.get(&left_local).unwrap_or_else(|| {
        ctx.crash_and_error(
            ctx.def_span(left),
            "Refined function must have a body (cannot be extern or abstract)",
        )
    });
    let right_thir = ctx.thir.get(&right_local).unwrap_or_else(|| {
        ctx.crash_and_error(
            ctx.def_span(right),
            "Refining function must have a body (cannot be extern or abstract)",
        )
    });
    check_refines_thir(ctx, left_thir, right_thir, ctx.def_span(left))
}

enum AnfStmt {
    /// LHS <- FUNC(EXPR0, ..., EXPRN)
    Call(ExprId, DefId, Box<[AnfRet]>),
    /// LHS <- EXPR
    Assign(AnfLhs, AnfRet),
    /// LHS <- if EXPR0 { EXPR1 } else { EXPR2 }
    If(ExprId, ExprId, Box<AnfRet>, Box<AnfRet>),
}

enum AnfLhs {
    Var(HirId),
}

enum AnfRet {
    Unit,
    Expr(ExprId),
    Var(HirId),
}

struct Anf {
    stmts: Vec<AnfStmt>,
    ret: AnfRet,
}

fn a_normal_form<'tcx>(ctx: TyCtxt<'tcx>, thir: &Thir<'tcx>, expr: ExprId) -> Anf {
    let mut stmts = Vec::new();
    let ret = a_normal_form_expr(ctx, thir, expr, &mut stmts);
    Anf { stmts, ret }
}

fn a_normal_form_expr<'tcx>(ctx: TyCtxt<'tcx>, thir: &Thir<'tcx>, expr: ExprId, stmts: &mut Vec<AnfStmt>) -> AnfRet {
    let expr = &thir[expr];
    use ExprKind::*;
    match &expr.kind {
        Scope { value, .. } => a_normal_form_expr(ctx, thir, *value, stmts),
        Block { block } => a_normal_form_block(ctx, thir, *block, stmts),
        VarRef { id } => AnfRet::Var(id.0),
        _ => ctx.crash_and_error(expr.span, format!("Unsupported expression in refine check: {expr:?}")),
    }
}

fn a_normal_form_block<'tcx>(ctx: TyCtxt<'tcx>, thir: &Thir<'tcx>, block: BlockId, stmts: &mut Vec<AnfStmt>) -> AnfRet {
    let block = &thir[block];
    let mut stmts = vec![];
    for stmt in &block.stmts {
        a_normal_form_stmt(ctx, thir, *stmt, &mut stmts);
    }
    match block.expr {
        None => AnfRet::Unit,
        Some(e) => a_normal_form_expr(ctx, thir, e, &mut stmts),
    }
}

fn a_normal_form_stmt<'tcx>(ctx: TyCtxt<'tcx>, thir: &Thir<'tcx>, block: StmtId, stmts: &mut Vec<AnfStmt>) {
    let stmt = &thir[block];
    use thir::StmtKind::*;
    match &stmt.kind {
        Expr { expr, .. } => {
            let _ = a_normal_form_expr(ctx, thir, *expr, stmts);
        }
        Let { pattern, initializer, else_block, span, .. } => {
            if let Some(_) = else_block {
                ctx.crash_and_error(*span, "Unsupported else block in refine check")
            }
            let Some(initializer) = initializer else {
                ctx.crash_and_error(*span, "Unsupported let without initializer in refine check")
            };
            if is_spec_or_refines_expr(ctx, thir, *initializer) {
                return
            }
            let rhs = a_normal_form_expr(ctx, thir, *initializer, stmts);

            let lhs = match pattern.kind {
                PatKind::Binding { var, .. } => AnfLhs::Var(var.0),
                _ => ctx.crash_and_error(*span, "Unsupported pattern in refine check"),
            };
            stmts.push(AnfStmt::Assign(lhs, rhs));
        }
    }
}

fn is_spec_or_refines_expr(tcx: TyCtxt, thir: &Thir, expr: ExprId) -> bool {
    let mut expr = &thir[expr];
    loop {
        match expr.kind {
            ExprKind::Scope { value, .. } => expr = &thir[value],
            ExprKind::Closure(box thir::ClosureExpr { closure_id, .. }) => {
                let closure_id = closure_id.to_def_id();
                return is_spec(tcx, closure_id) || is_refines(tcx, closure_id)
            }
            _ => return false,
        }
    }
}

struct RefineChecker<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    left: &'a Thir<'tcx>,
    right: &'a Thir<'tcx>,
    refine_hir_id: HashMap<HirId, HirId>,
    span: Span,
}

impl<'a, 'tcx> RefineChecker<'a, 'tcx> {
    fn new(
        ctx: &'a TranslationCtx<'tcx>,
        left: &'a Thir<'tcx>,
        right: &'a Thir<'tcx>,
        span: Span,
    ) -> Self {
        let refine_hir_id = HashMap::new();
        let mut checker = RefineChecker { ctx, left, right, refine_hir_id, span };
        checker.refine_params();
        checker
    }

    fn refine_params(&mut self) {
        let left = self.left;
        let right = self.right;
        let mut right_params = right.params.iter();
        for left_p in left.params.iter() {
            if is_ghost_ty_(self.ctx.tcx, left_p.ty) {
                continue;
            }
            let Some(right_p) = right_params.next() else {
                self.ctx.crash_and_error(
                    self.span,
                    "Refining function has more non-ghost parameters than the refined function",
                )
            };
            let Some(left_p) = &left_p.pat else { continue; };
            let Some(right_p) = &right_p.pat else {
                self.ctx.crash_and_error(
                    self.span,
                    "Refining function has more non-ghost parameters than the refined function",
                )
            };
            self.refine_pats(&left_p, &right_p);
        }
    }

    fn refine_pats(&mut self, left: &thir::Pat<'tcx>, right: &thir::Pat<'tcx>) {
        match (&left.kind, &right.kind) {
            (PatKind::Binding { var: l, .. }, PatKind::Binding { var: r, .. }) => {
                self.refine_hir_id.insert(l.0, r.0);
            }
            _ => self.ctx.crash_and_error(
                self.span,
                "Refining and refined functions must have the same parameter patterns",
            ),
        }
    }

    fn refines(&self, left: Anf, right: Anf) {
        if left.stmts.len() != 0 || right.stmts.len() != 0 {
            self.ctx.crash_and_error(
                self.span,
                "Refining and refined functions must have a single expression body",
            )
        }
        match (left.ret, right.ret) {
            (AnfRet::Unit, AnfRet::Unit) => {}
            (AnfRet::Expr(l), AnfRet::Expr(r)) => {
                self.ctx.crash_and_error(
                    self.left[l].span,
                    "TODO",
                )
            }
            (AnfRet::Var(l), AnfRet::Var(r)) => {
                let r_ = self.refine_hir_id.get(&l).unwrap_or_else(|| {
                    eprintln!("{:?}", self.refine_hir_id);
                    eprintln!("{:#?}", self.left);
                    self.ctx.crash_and_error(
                        self.ctx.hir_span(l),
                        format!("{l:?} does not refine {r:?}"),
                    )
                });
                if *r_ != r {
                    self.ctx.crash_and_error(
                        self.ctx.hir_span(l),
                        format!("{l:?} does not refine {r:?} ({l:?} refines {r_:?})"),
                    )
                }
            }
            _ => {
                self.ctx.crash_and_error(
                    self.span,
                    "Refining and refined functions must have the same return kind",
                )
            }
        }
    }
}

fn check_refines_thir<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    (left_thir, left_expr): &(Thir<'tcx>, ExprId),
    (right_thir, right_expr): &(Thir<'tcx>, ExprId),
    span: Span,
) {
    let checker = RefineChecker::new(ctx, left_thir, right_thir, span);
    let left = a_normal_form(ctx.tcx, left_thir, *left_expr);
    let right = a_normal_form(ctx.tcx, right_thir, *right_expr);
    checker.refines(left, right);
}
