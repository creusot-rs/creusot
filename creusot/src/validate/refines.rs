use std::collections::HashMap;

use either::Either;
use rustc_ast::{BindingMode, ByRef, Mutability};
use rustc_hir::{HirId, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::BinOp,
    thir::{self, BlockId, ExprId, ExprKind, PatKind, StmtId, Thir},
    ty::{self, ParamConst, TyCtxt},
};
use rustc_span::{ErrorGuaranteed, Span};
use rustc_type_ir::TyKind::Error;

use crate::{
    contracts_items::{is_refines, is_spec},
    ctx::{HasTyCtxt, TranslationCtx},
    validate::ghost::is_ghost_ty_,
};

pub(crate) fn validate_refines(ctx: &TranslationCtx) {
    let mut err = Ok(());
    for (left, right) in ctx.refines.iter() {
        err = check_refines(ctx, *left, right.resolved).and(err);
    }
    err.unwrap_or_else(|e| e.raise_fatal())
}

fn check_refines<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    left: DefId,
    (right, subst2): (DefId, ty::GenericArgsRef<'tcx>),
) -> Result<(), ErrorGuaranteed> {
    let Some(left_local) = left.as_local() else {
        return Err(ctx.error(ctx.def_span(left), "Refining function must be local").emit());
    };
    let Some(right_local) = right.as_local() else {
        return Err(ctx
            .error(
                ctx.def_span(right),
                "Refined function must be local (refining extern functions is not implemented)",
            )
            .emit());
    };
    let Some(left_thir) = ctx.thir.get(&left_local) else {
        return Err(ctx
            .error(
                ctx.def_span(left),
                "Refining function must have a body (cannot be extern or abstract)",
            )
            .emit());
    };
    let Some(right_thir) = ctx.thir.get(&right_local) else {
        return Err(ctx
            .error(
                ctx.def_span(right),
                "Refined function must have a body (cannot be extern or abstract)",
            )
            .emit());
    };
    check_refines_thir(ctx, left_thir, right_thir, subst2, ctx.def_span(left))
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
enum AnfStmt<'tcx> {
    /// LHS <- FUNC(EXPR0, ..., EXPRN)
    Call(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        ExprId,
        DefId,
        ty::GenericArgsRef<'tcx>,
        Box<[AnfValue<'tcx>]>,
        Span,
    ),
    /// LHS <- EXPR OP EXPR
    Binop(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        ExprId,
        AnfValue<'tcx>,
        BinOp,
        AnfValue<'tcx>,
        Span,
    ),
    /// let mut VAR
    LetMut(HirId),
    /// LHS <- EXPR
    Assign(AnfLhs, AnfValue<'tcx>),
    /// LHS <- if EXPR0 { EXPR1 } else { EXPR2 }
    If(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        ExprId,
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        ExprId,
        Box<AnfValue<'tcx>>,
        Box<AnfValue<'tcx>>,
    ),
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
enum AnfLhs {
    Var(HirId),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable)]
enum AnfValue<'tcx> {
    Unit,
    Expr(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        ExprId,
    ),
    Var(HirId),
    Fn(DefId, ty::GenericArgsRef<'tcx>),
    Literal(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        rustc_ast::LitKind,
        bool,
    ),
    Const(ty::Const<'tcx>),
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
struct Anf<'tcx> {
    stmts: Vec<AnfStmt<'tcx>>,
    ret: AnfValue<'tcx>,
}

/// State for computing A-normal form
struct AnfContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    /// Mapping from ANF variables to values
    /// This lets us identify `let x = e; f(x)` with `f(e)`.
    alias: HashMap<Either<HirId, ExprId>, AnfValue<'tcx>>,
}

fn a_normal_form<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    expr: ExprId,
) -> Result<Anf<'tcx>, ErrorGuaranteed> {
    let mut ctx = AnfContext::new(tcx, thir);
    let mut stmts = Vec::new();
    let ret = ctx.a_normal_form_expr(expr, &mut stmts)?;
    Ok(Anf { stmts, ret })
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for AnfContext<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'a, 'tcx> AnfContext<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, thir: &'a Thir<'tcx>) -> Self {
        let alias = HashMap::new();
        AnfContext { tcx, thir, alias }
    }

    fn hir_id_value(&self, hir_id: HirId) -> AnfValue<'tcx> {
        self.alias.get(&Either::Left(hir_id)).cloned().unwrap_or(AnfValue::Var(hir_id))
    }

    fn expr_id_value(&self, expr_id: ExprId) -> AnfValue<'tcx> {
        self.alias.get(&Either::Right(expr_id)).cloned().unwrap_or(AnfValue::Expr(expr_id))
    }

    fn a_normal_form_expr(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<AnfValue<'tcx>, ErrorGuaranteed> {
        let expr = &self.thir[expr_id];
        use ExprKind::*;
        let value = match &expr.kind {
            Scope { value, .. } => self.a_normal_form_expr(*value, stmts)?,
            Block { block } => self.a_normal_form_block(*block, stmts)?,
            VarRef { id } => self.hir_id_value(id.0),
            Call { fun, args, fn_span, .. } => {
                let fun = self.a_normal_form_expr(*fun, stmts)?;
                match fun {
                    AnfValue::Fn(fun_id, subst) => {
                        let args = args
                            .iter()
                            .map(|arg| self.a_normal_form_expr(*arg, stmts))
                            .collect::<Result<::std::boxed::Box<[_]>, ErrorGuaranteed>>()?;
                        stmts.push(AnfStmt::Call(expr_id, fun_id, subst, args, *fn_span));
                        AnfValue::Expr(expr_id)
                    }
                    _ => self.crash_and_error(
                        expr.span,
                        "Unsupported function expression in refine check:\n{fun:?}",
                    ),
                }
            }
            ZstLiteral { .. } => match expr.ty.kind() {
                ty::TyKind::FnDef(def_id, subst) => AnfValue::Fn(*def_id, subst),
                _ => AnfValue::Unit,
            },
            Binary { op, lhs, rhs } => {
                let lhs = self.a_normal_form_expr(*lhs, stmts)?;
                let rhs = self.a_normal_form_expr(*rhs, stmts)?;
                stmts.push(AnfStmt::Binop(expr_id, lhs, *op, rhs, expr.span));
                AnfValue::Expr(expr_id)
            }
            Literal { lit, neg } => AnfValue::Literal(lit.node, *neg),
            ConstParam { param, .. } => AnfValue::Const(ty::Const::new_param(self.tcx, *param)),
            _ => self.crash_and_error(
                expr.span,
                format!("Unsupported expression in refine check:\n{expr:?}"),
            ),
        };
        self.alias.insert(Either::Right(expr_id), value.clone());
        Ok(value)
    }

    fn a_normal_form_block(
        &mut self,
        block: BlockId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<AnfValue<'tcx>, ErrorGuaranteed> {
        let block = &self.thir[block];
        for stmt in &block.stmts {
            self.a_normal_form_stmt(*stmt, stmts)?;
        }
        match block.expr {
            None => Ok(AnfValue::Unit),
            Some(e) => self.a_normal_form_expr(e, stmts),
        }
    }

    fn a_normal_form_stmt(
        &mut self,
        stmt: StmtId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<(), ErrorGuaranteed> {
        let stmt = &self.thir[stmt];
        use thir::StmtKind::*;
        match &stmt.kind {
            Expr { expr, .. } => {
                let _ = self.a_normal_form_expr(*expr, stmts)?;
            }
            Let { pattern, initializer, else_block, span, .. } => {
                if let Some(_) = else_block {
                    return Err(self.error(*span, "Unsupported let-else in refine check").emit());
                }
                let Some(initializer) = initializer else {
                    return Err(self
                        .error(*span, "Unsupported let without initializer in refine check")
                        .emit());
                };
                if is_spec_or_refines_expr(self.tcx, self.thir, *initializer) {
                    return Ok(());
                }
                let rhs = self.a_normal_form_expr(*initializer, stmts)?;
                match pattern.kind {
                    PatKind::Binding { subpattern: Some(_), .. } => {
                        return Err(self
                            .error(*span, "Unsupported @ subpattern in refine check")
                            .emit());
                    }
                    PatKind::Binding {
                        var, mode: BindingMode(ByRef::No, Mutability::Not), ..
                    } => {
                        self.alias.insert(Either::Left(var.0), rhs.clone());
                    }
                    PatKind::Binding {
                        var, mode: BindingMode(ByRef::No, Mutability::Mut), ..
                    } => {
                        stmts.push(AnfStmt::LetMut(var.0));
                        stmts.push(AnfStmt::Assign(AnfLhs::Var(var.0), rhs));
                    }
                    _ => {
                        return Err(self
                            .error(*span, "Unsupported pattern in refine check")
                            .emit());
                    }
                };
            }
        }
        Ok(())
    }
}

fn is_spec_or_refines_expr(tcx: TyCtxt, thir: &Thir, expr: ExprId) -> bool {
    let mut expr = &thir[expr];
    loop {
        match expr.kind {
            ExprKind::Scope { value, .. } => expr = &thir[value],
            ExprKind::Closure(box thir::ClosureExpr { closure_id, .. }) => {
                let closure_id = closure_id.to_def_id();
                return is_spec(tcx, closure_id) || is_refines(tcx, closure_id);
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
    refine_expr_id: HashMap<ExprId, ExprId>,
    span: Span,
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for RefineChecker<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}

impl<'a, 'tcx> RefineChecker<'a, 'tcx> {
    fn new(
        ctx: &'a TranslationCtx<'tcx>,
        left: &'a Thir<'tcx>,
        right: &'a Thir<'tcx>,
        span: Span,
    ) -> Self {
        let refine_hir_id = HashMap::new();
        let refine_expr_id = HashMap::new();
        RefineChecker { ctx, left, right, refine_hir_id, refine_expr_id, span }
    }

    fn refine_params(&mut self) -> Result<(), ErrorGuaranteed> {
        let left = self.left;
        let right = self.right;
        let mut right_params = right.params.iter();
        for left_p in left.params.iter() {
            if is_ghost_ty_(self.ctx.tcx, left_p.ty) {
                continue;
            }
            let Some(right_p) = right_params.next() else {
                return Err(self
                    .error(
                        self.span,
                        "Refining function has more non-ghost parameters than the refined function",
                    )
                    .emit());
            };
            let Some(left_p) = &left_p.pat else {
                continue;
            };
            let Some(right_p) = &right_p.pat else {
                return Err(self
                    .error(
                        self.span,
                        "Refining function has more non-ghost parameters than the refined function",
                    )
                    .emit());
            };
            self.refine_pats(&left_p, &right_p)?;
        }
        Ok(())
    }

    fn refine_pats(
        &mut self,
        left: &thir::Pat<'tcx>,
        right: &thir::Pat<'tcx>,
    ) -> Result<(), ErrorGuaranteed> {
        match (&left.kind, &right.kind) {
            (PatKind::Binding { var: l, .. }, PatKind::Binding { var: r, .. }) => {
                self.refine_hir_id.insert(l.0, r.0);
                Ok(())
            }
            _ => Err(self
                .error(
                    self.span,
                    "Refining and refined functions must have the same parameter patterns",
                )
                .emit()),
        }
    }

    fn refine_value(&self, v1: &AnfValue<'tcx>, v2: &AnfValue<'tcx>) -> bool {
        match (v1, v2) {
            (AnfValue::Unit, AnfValue::Unit) => true,
            (AnfValue::Expr(e1), AnfValue::Expr(e2)) => {
                let Some(e1_) = self.refine_expr_id.get(e1) else { return false };
                e1_ == e2
            }
            (AnfValue::Var(v1), AnfValue::Var(v2)) => {
                let v1_ = self.refine_hir_id[v1];
                v1_ == *v2
            }
            (AnfValue::Literal(lit1, neg1), AnfValue::Literal(lit2, neg2)) => {
                lit1 == lit2 && neg1 == neg2
            }
            (AnfValue::Const(p1), AnfValue::Const(p2)) => match (p1.kind(), p2.kind()) {
                (ty::ConstKind::Param(p1), ty::ConstKind::Param(p2)) => p1 == p2,
                _ => false,
            },
            _ => false,
        }
    }

    fn refine_subst(
        &self,
        subst1: ty::GenericArgsRef<'tcx>,
        subst2: ty::GenericArgsRef<'tcx>,
        span1: Span,
        _span2: Span,
    ) -> Result<(), ErrorGuaranteed> {
        assert!(subst1.len() == subst2.len());
        for (i, (arg1, arg2)) in subst1.into_iter().zip(subst2).enumerate() {
            if arg1 != arg2 {
                return Err(self
                    .error(span1, format!("Generic argument mismatch\n{arg1:?} != {arg2:?}"))
                    .emit());
            }
        }
        Ok(())
    }

    fn refine_args(
        &self,
        args1: &[AnfValue<'tcx>],
        args2: &[AnfValue<'tcx>],
        span1: Span,
        _span2: Span,
    ) -> Result<(), ErrorGuaranteed> {
        if args1.len() != args2.len() {
            return Err(self
                .error(
                    span1,
                    "Refining and refined functions must have the same number of arguments",
                )
                .emit());
        }
        for (i, (arg1, arg2)) in args1.into_iter().zip(args2).enumerate() {
            if !self.refine_value(arg1, arg2) {
                return Err(self.ctx.error(span1, format!("Argument {i} mismatch")).emit());
            }
        }
        Ok(())
    }

    fn refine_result(&mut self, lhs1: &ExprId, lhs2: &ExprId) {
        self.refine_expr_id.insert(*lhs1, *lhs2);
    }

    fn refine_stmts(
        &mut self,
        left: &[AnfStmt<'tcx>],
        right: &[AnfStmt<'tcx>],
    ) -> Result<(), ErrorGuaranteed> {
        let mut right = right.into_iter();
        for left in left.into_iter() {
            match left {
                AnfStmt::Call(lhs1, fun1, subst1, args1, span1) => {
                    match right.next() {
                        Some(AnfStmt::Call(lhs2, fun2, subst2, args2, span2)) => {
                            if fun1 == fun2 {
                                self.refine_subst(subst1, subst2, *span1, *span2)?;
                                self.refine_args(&**args1, args2, *span1, *span2)?;
                                self.refine_result(lhs1, lhs2);
                            } else if let Some(fun2_) = self.ctx.refines(*fun1)
                                && fun2_.thir.0 == *fun2
                            {
                                let subst1 = ty::EarlyBinder::bind(fun2_.thir.1)
                                    .instantiate(self.ctx.tcx, subst1);
                                self.refine_subst(subst1, subst2, *span1, *span2)?;
                                self.refine_args(&**args1, args2, *span1, *span2)?;
                                self.refine_result(lhs1, lhs2);
                            } else {
                                return Err(self
                                    .error(*span1, format!("TODO {fun1:?} {fun2:?}"))
                                    .emit());
                            }
                        }
                        Some(_) => return Err(self.error(self.span, "mismatch TODO").emit()),
                        None => return Err(self
                            .error(
                                self.span,
                                "Refining function has more statements than the refined function",
                            )
                            .emit()),
                    }
                }
                AnfStmt::Binop(lhs1, v1, op1, w1, span1) => match right.next() {
                    Some(AnfStmt::Binop(lhs2, v2, op2, w2, span2)) => {
                        if op1 == op2 && self.refine_value(v1, v2) && self.refine_value(w1, w2) {
                            self.refine_result(lhs1, lhs2);
                        } else {
                            return Err(self.error(
                                *span1,
                                format!(
                                    "Refining binary operation does not match refined operation: {v1:?} {op1:?} {w1:?} vs {v2:?} {op2:?} {w2:?}"
                                ),
                            ).emit());
                        }
                    }
                    Some(_) => return Err(self.error(self.span, "mismatch TODO").emit()),
                    None => {
                        return Err(self
                            .error(
                                self.span,
                                "Refining function has more statements than the refined function",
                            )
                            .emit());
                    }
                },
                AnfStmt::LetMut(v) => todo!(),
                AnfStmt::Assign(anf_lhs, anf_ret) => todo!(),
                AnfStmt::If(expr_id, expr_id1, anf_ret, anf_ret1) => todo!(),
            }
        }
        if let Some(_) = right.next() {
            return Err(self
                .error(
                    self.span,
                    "Refining function has fewer statements than the refined function",
                )
                .emit());
        }
        Ok(())
    }

    fn refines(&mut self, left: &Anf<'tcx>, right: &Anf<'tcx>) -> Result<(), ErrorGuaranteed> {
        self.refine_stmts(&left.stmts, &right.stmts)?;
        if self.refine_value(&left.ret, &right.ret) {
            Ok(())
        } else {
            Err(self.error(self.span, "Return value mismatch").emit())
        }
    }
}

fn check_refines_thir<'a, 'tcx>(
    ctx: &TranslationCtx<'tcx>,
    (left_thir, left_expr): &'a (Thir<'tcx>, ExprId),
    (right_thir, right_expr): &'a (Thir<'tcx>, ExprId),
    subst2: ty::GenericArgsRef<'tcx>,
    span: Span,
) -> Result<(), ErrorGuaranteed> {
    let left = a_normal_form(ctx.tcx, left_thir, *left_expr)?;
    let right = a_normal_form(ctx.tcx, right_thir, *right_expr)?;
    let right = ty::EarlyBinder::bind(right).instantiate(ctx.tcx, subst2);
    let mut checker = RefineChecker::new(ctx, left_thir, right_thir, span);
    checker.refine_params()?;
    checker.refines(&left, &right)
}
