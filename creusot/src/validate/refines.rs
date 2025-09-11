use std::collections::{HashMap, HashSet};

use either::Either;
use rustc_ast::{BindingMode, BorrowKind, ByRef, Mutability};
use rustc_hir::{HirId, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{self, BinOp},
    thir::{self, BlockId, ExprId, ExprKind, PatKind, StmtId, Thir},
    ty::{self, TyCtxt},
};
use rustc_session::HashStableContext;
use rustc_span::{ErrorGuaranteed, Span};

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TypeVisitable, TypeFoldable)]
enum Var {
    HirId(HirId),
    ExprId(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        ExprId,
    ),
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
struct AnfStmt<'tcx> {
    lhs: Var,
    rhs: AnfAction<'tcx>,
    span: Span,
}

/// We inline values into statements. The alternative is to bind constants to variables,
/// but that makes later passes more complicated to deal with the fact that these bindings
/// have no effect and should commute with other assignments.
///
/// That makes it easier to deal with case like this:
/// ```
/// f(1, g())
/// ```
/// has the same ANF (in this representation) as
/// ```
/// let x = g(); f(1, x)
/// ```
#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
enum AnfAction<'tcx> {
    Value(AnfValue<'tcx>),
    /// FUNC(EXPR0, ..., EXPRN)
    Call(DefId, ty::GenericArgsRef<'tcx>, Box<[AnfValue<'tcx>]>),
    /// EXPR OP EXPR
    Binop(AnfValue<'tcx>, BinOp, AnfValue<'tcx>),
    /// Read a mutable variable
    Read(HirId),
    Deref(AnfValue<'tcx>),
    /// if EXPR0 { EXPR1 } else { EXPR2 }
    If(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        ExprId,
        Box<AnfValue<'tcx>>,
        Box<AnfValue<'tcx>>,
    ),
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
enum AnfLhs {
    Var(Var),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable)]
enum AnfValue<'tcx> {
    Unit,
    Var(Var),
    Fn(DefId, ty::GenericArgsRef<'tcx>),
    Literal(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        rustc_ast::LitKind,
        bool,
    ),
    Const(ty::Const<'tcx>),
    Borrow(Box<AnfPlace<'tcx>>),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable)]
struct AnfPlace<'tcx> {
    base: AnfPlaceBase<'tcx>,
    projections: Vec<AnfProjection>,
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable)]
enum AnfProjection {
    Deref,
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable)]
enum AnfPlaceBase<'tcx> {
    MutVar(Var),
    /// This ANF conversion may skip binding immutable variables, so we record their value here instead.
    ImmutVar(AnfValue<'tcx>),
}

impl<'tcx> AnfPlace<'tcx> {
    fn mut_var(var: Var) -> Self {
        AnfPlace { base: AnfPlaceBase::MutVar(var), projections: vec![] }
    }

    fn immut(value: AnfValue<'tcx>) -> Self {
        AnfPlace { base: AnfPlaceBase::ImmutVar(value), projections: vec![] }
    }

    fn add_deref(&mut self) {
        self.projections.push(AnfProjection::Deref);
    }
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
    /// `None` means the variable is mutable
    alias: HashMap<HirId, Option<AnfValue<'tcx>>>,
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

    fn a_normal_form_expr(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<AnfValue<'tcx>, ErrorGuaranteed> {
        let expr = &self.thir[expr_id];
        use ExprKind::*;
        match &expr.kind {
            Scope { value, .. } => self.a_normal_form_expr(*value, stmts),
            Block { block } => self.a_normal_form_block(*block, stmts),
            VarRef { id } => match &self.alias.get(&id.0) {
                None | Some(None) => Ok(AnfValue::Var(Var::HirId(id.0))),
                Some(Some(v)) => Ok(v.clone()),
            },
            Call { fun, args, fn_span, .. } => {
                let fun = self.a_normal_form_expr(*fun, stmts)?;
                match fun {
                    AnfValue::Fn(fun_id, subst) => {
                        let args = args
                            .iter()
                            .map(|arg| self.a_normal_form_expr(*arg, stmts))
                            .collect::<Result<::std::boxed::Box<[_]>, ErrorGuaranteed>>()?;
                        stmts.push(AnfStmt {
                            lhs: Var::ExprId(expr_id),
                            rhs: AnfAction::Call(fun_id, subst, args),
                            span: *fn_span,
                        });
                        Ok(AnfValue::Var(Var::ExprId(expr_id)))
                    }
                    _ => self.crash_and_error(
                        expr.span,
                        "Unsupported function expression in refine check:\n{fun:?}",
                    ),
                }
            }
            ZstLiteral { .. } => match expr.ty.kind() {
                ty::TyKind::FnDef(def_id, subst) => Ok(AnfValue::Fn(*def_id, subst)),
                _ => Ok(AnfValue::Unit),
            },
            Binary { op, lhs, rhs } => {
                let lhs = self.a_normal_form_expr(*lhs, stmts)?;
                let rhs = self.a_normal_form_expr(*rhs, stmts)?;
                stmts.push(AnfStmt {
                    lhs: Var::ExprId(expr_id),
                    rhs: AnfAction::Binop(lhs, *op, rhs),
                    span: expr.span,
                });
                Ok(AnfValue::Var(Var::ExprId(expr_id)))
            }
            Literal { lit, neg } => Ok(AnfValue::Literal(lit.node, *neg)),
            ConstParam { param, .. } => Ok(AnfValue::Const(ty::Const::new_param(self.tcx, *param))),
            Deref { arg } => {
                let arg = self.a_normal_form_expr(*arg, stmts)?;
                stmts.push(AnfStmt {
                    lhs: Var::ExprId(expr_id),
                    rhs: AnfAction::Deref(arg),
                    span: expr.span,
                });
                Ok(AnfValue::Var(Var::ExprId(expr_id)))
            }
            // THIR inserts some &*, we simplify them
            Borrow { arg, .. } if let Deref { arg } = &self.thir[*arg].kind => {
                self.a_normal_form_expr(*arg, stmts)
            }
            Borrow { arg, .. } => {
                let place = self.a_normal_form_place(*arg, stmts)?;
                Ok(AnfValue::Borrow(std::boxed::Box::new(place)))
            }
            _ => self.crash_and_error(
                expr.span,
                format!("Unsupported expression in refine check:\n{expr:?}"),
            ),
        }
    }

    fn a_normal_form_place(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<AnfPlace<'tcx>, ErrorGuaranteed> {
        let expr = &self.thir[expr_id];
        use ExprKind::*;
        match &expr.kind {
            VarRef { id } => match &self.alias.get(&id.0) {
                None | Some(None) => Ok(AnfPlace::mut_var(Var::HirId(id.0))),
                Some(Some(v)) => Ok(AnfPlace::immut(v.clone())),
            },
            Deref { arg } => {
                let mut place = self.a_normal_form_place(*arg, stmts)?;
                place.add_deref();
                Ok(place)
            }
            Scope { value, .. } => self.a_normal_form_place(*value, stmts),
            _ => {
                let v = self.a_normal_form_expr(expr_id, stmts)?;
                if let AnfValue::Var(Var::ExprId(expr_id2)) = v
                    && expr_id2 == expr_id
                {
                    // expr_id was just bound so we can use it as a place
                    Ok(AnfPlace::mut_var(Var::ExprId(expr_id)))
                } else {
                    // we create a place for expr_id
                    stmts.push(AnfStmt {
                        lhs: Var::ExprId(expr_id),
                        rhs: AnfAction::Value(v.clone()),
                        span: expr.span,
                    });
                    Ok(AnfPlace::mut_var(Var::ExprId(expr_id)))
                }
            }
        }
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
                        self.alias.insert(var.0, Some(rhs.clone()));
                    }
                    PatKind::Binding {
                        var, mode: BindingMode(ByRef::No, Mutability::Mut), ..
                    } => {
                        self.alias.insert(var.0, None);
                        stmts.push(AnfStmt {
                            lhs: Var::HirId(var.0),
                            rhs: AnfAction::Value(rhs),
                            span: self.thir[*initializer].span,
                        });
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
    refine_var: HashMap<Var, Var>,
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
        let refine_var = HashMap::new();
        RefineChecker { ctx, left, right, refine_var, span }
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
                self.refine_var.insert(Var::HirId(l.0), Var::HirId(r.0));
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
            (AnfValue::Var(v1), AnfValue::Var(v2)) => {
                let Some(v1_) = self.refine_var.get(v1) else { return false };
                v1_ == v2
            }
            (AnfValue::Literal(lit1, neg1), AnfValue::Literal(lit2, neg2)) => {
                lit1 == lit2 && neg1 == neg2
            }
            (AnfValue::Const(p1), AnfValue::Const(p2)) => p1 == p2,
            (AnfValue::Borrow(place1), AnfValue::Borrow(place2)) => {
                self.refine_place(place1, place2)
            }
            _ => false,
        }
    }

    fn refine_place(&self, p1: &AnfPlace<'tcx>, p2: &AnfPlace<'tcx>) -> bool {
        let refine_base = match (&p1.base, &p2.base) {
            (AnfPlaceBase::MutVar(v1), AnfPlaceBase::MutVar(v2)) => {
                let Some(v1_) = self.refine_var.get(v1) else { return false };
                v1_ == v2
            }
            (AnfPlaceBase::ImmutVar(v1), AnfPlaceBase::ImmutVar(v2)) => self.refine_value(v1, v2),
            _ => false,
        };
        refine_base && p1.projections == p2.projections
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

    fn refine_args<'b>(
        &self,
        args1: impl ExactSizeIterator<Item = &'b AnfValue<'tcx>>,
        args2: &[AnfValue<'tcx>],
        span1: Span,
        _span2: Span,
    ) -> Result<(), ErrorGuaranteed>
    where
        'tcx: 'b,
    {
        if args1.len() != args2.len() {
            return Err(self
                .error(
                    span1,
                    "Refining and refined functions must have the same number of arguments",
                )
                .emit());
        }
        for (i, (arg1, arg2)) in args1.zip(args2).enumerate() {
            if !self.refine_value(arg1, arg2) {
                return Err(self.ctx.error(span1, format!("Argument {i} mismatch")).emit());
            }
        }
        Ok(())
    }

    fn refine_result(&mut self, lhs1: &ExprId, lhs2: &ExprId) {
        self.new_var(Var::ExprId(*lhs1), Var::ExprId(*lhs2));
    }

    fn new_var(&mut self, v1: Var, v2: Var) {
        self.refine_var.insert(v1, v2);
    }

    fn refine_stmts(
        &mut self,
        left: &[AnfStmt<'tcx>],
        right: &[AnfStmt<'tcx>],
    ) -> Result<(), ErrorGuaranteed> {
        let mut right = right.into_iter();
        for left in left.into_iter() {
            let Some(right) = right.next() else {
                return Err(self
                    .error(
                        left.span,
                        "Refining function has more statements than the refined function",
                    )
                    .emit());
            };
            match (&left.rhs, &right.rhs) {
                (AnfAction::Call(fun1, subst1, args1), AnfAction::Call(fun2, subst2, args2)) => {
                    if fun1 == fun2 {
                        self.refine_subst(subst1, subst2, left.span, right.span)?;
                        self.refine_args(args1.into_iter(), args2, left.span, right.span)?;
                    } else if let Some(fun2_) = self.ctx.refines(*fun1)
                        && fun2_.thir.0 == *fun2
                    {
                        let subst1 =
                            ty::EarlyBinder::bind(fun2_.thir.1).instantiate(self.ctx.tcx, subst1);
                        let args1: Box<[_]> = args1
                            .into_iter()
                            .zip(&fun2_.erase_args)
                            .filter_map(|(arg, &erase)| if erase { None } else { Some(arg) })
                            .collect();
                        self.refine_subst(subst1, subst2, left.span, right.span)?;
                        self.refine_args(args1.into_iter(), args2, left.span, right.span)?;
                    } else {
                        return Err(self
                            .error(left.span, "Function call mismatch")
                            .with_span_note(right.span, "refined call")
                            .emit());
                    }
                }
                (AnfAction::Binop(v1, op1, w1), AnfAction::Binop(v2, op2, w2)) => {
                    if !(op1 == op2 && self.refine_value(v1, v2) && self.refine_value(w1, w2)) {
                        return Err(self
                            .error(left.span, "Binary op mismatch")
                            .with_span_note(right.span, "refined operator")
                            .emit());
                    }
                }
                (AnfAction::Deref(v1), AnfAction::Deref(v2)) => {
                    if !self.refine_value(v1, v2) {
                        return Err(self
                            .error(left.span, "deref mismatch")
                            .with_span_note(right.span, "refined deref")
                            .emit());
                    }
                }
                (AnfAction::Value(v1), AnfAction::Value(v2)) => {
                    if !self.refine_value(v1, v2) {
                        return Err(self
                            .error(left.span, "value mismatch")
                            .with_span_note(right.span, "refined value")
                            .emit());
                    }
                }
                (AnfAction::Read(v1), AnfAction::Read(v2)) => {
                    if let Some(v1_) = self.refine_var.get(&Var::HirId(*v1)) {
                        if *v1_ != Var::HirId(*v2) {
                            return Err(self
                                .error(left.span, "read variable mismatch")
                                .with_span_note(right.span, "refined read")
                                .emit());
                        }
                    }
                }
                (l, r) => {
                    return Err(self
                        .error(
                            left.span,
                            format!("Statement kind mismatch\n {l:?} does not refine {r:?}"),
                        )
                        .with_span_note(right.span, "refined statement")
                        .emit());
                }
            }
            self.new_var(left.lhs, right.lhs);
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
    checker.refines(&left, &right).map_err(|e| {
        eprintln!("{left:#?}\n{right:#?}");
        e
    })
}
