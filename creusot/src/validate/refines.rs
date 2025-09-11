//! The `#[refines]` check
//!
//! The main challenge is to equate
//! ```
//! g(f(x))
//! ```
//! and
//! ```
//! let y = f(x);
//! g(y)
//! ```
//! (We often expand expressions like that to insert `ghost!` blocks.)
//!
//! We solve that by transforming THIR expressions to A-normal form.
use std::collections::HashMap;

use rustc_ast::{BindingMode, ByRef, Mutability};
use rustc_hir::{HirId, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::{
    middle::region::ScopeTree,
    mir::BinOp,
    thir::{self, BlockId, ExprId, ExprKind, PatKind, StmtId, Thir},
    ty::{self, TyCtxt},
};
use rustc_span::{ErrorGuaranteed, Span};

use crate::{
    backend::is_trusted_item,
    contracts_items::{is_refines, is_spec},
    ctx::{HasTyCtxt, TranslationCtx},
    validate::{ghost::is_ghost_ty_, is_ghost_block},
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
    if is_trusted_item(ctx.tcx, left) {
        return Ok(());
    }
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
    let left_scope = ctx.tcx.region_scope_tree(left);
    let right_scope = ctx.tcx.region_scope_tree(right);
    check_refines_thir(
        ctx,
        (left_thir, left_scope),
        (right_thir, right_scope),
        subst2,
        ctx.def_span(left),
        ctx.def_span(right),
    )
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
struct AnfBlock<'tcx> {
    stmts: Vec<AnfStmt<'tcx>>,
    ret: (AnfValue<'tcx>, Span),
    span: Span,
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
struct AnfFn<'tcx> {
    args: Vec<AnfPattern>,
    body: AnfBlock<'tcx>,
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
    pattern: AnfPattern,
    rhs: AnfOp<'tcx>,
    span: Span,
}

/// Operation
///
/// This is a generic representation where all enum tags are factored into the first field
/// and the other fields contain the subtrees.
/// This makes the refinement check almost trivial: compare the tags, then compare the fields.
/// For example an addition would be represented as `GenericOp(Binop(Add), box [lhs, rhs], box [])`.
///
/// The second field contains by-value operands (arguments of function calls, binary operators,
/// `if` and `match` scrutinees, assignment lvalues and rvalues).
///
/// The third field contains sub-blocks of control structures (`if`, `match`, `let-else`).
/// For constructs other than `match`, the arms have their `pattern` field default to `Wild`.
///
/// When comparing two ASTs, if the `GenericOp` tag matches, then the second fields
/// must have the same length. But the third fields may differ in length (e.g., `match`
/// with different arms, `if` (or `let`) with or without `else`)
///
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
struct AnfOp<'tcx> {
    tag: OpTag<'tcx>,
    args: Box<[(AnfValue<'tcx>, Span)]>,
    arms: Box<[AnfArm<'tcx>]>,
}

impl<'tcx> AnfOp<'tcx> {
    fn by_value(tag: OpTag<'tcx>, args: Box<[(AnfValue<'tcx>, Span)]>) -> Self {
        Self { tag, args, arms: [].into() }
    }

    fn control(
        tag: OpTag<'tcx>,
        args: Box<[(AnfValue<'tcx>, Span)]>,
        arms: Box<[AnfArm<'tcx>]>,
    ) -> Self {
        Self { tag, args, arms }
    }
}

/// Tag for `AnfOp`
#[derive(Clone, Copy, Debug, PartialEq, TypeVisitable, TypeFoldable)]
enum OpTag<'tcx> {
    Value,
    Deref,
    Read,
    Binop(BinOp),
    If,
    Match,
    Call(DefId, ty::GenericArgsRef<'tcx>),
    LetElse,
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
struct AnfArm<'tcx> {
    pattern: AnfPattern,
    body: AnfBlock<'tcx>,
    span: Span,
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable)]
enum AnfPattern {
    Wild,
    Var(Var),
    Ctor(Ctor, Box<[AnfPattern]>, Span),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable)]
enum AnfValue<'tcx> {
    Zst,
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
    Ctor(Ctor, Box<[(AnfValue<'tcx>, Span)]>),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable)]
enum Ctor {
    Adt(DefId),
    Tuple,
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

/// State for computing A-normal form
struct AnfContext<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    thir: &'a Thir<'tcx>,
    scope_tree: &'a ScopeTree,
    /// Mapping from ANF variables to values
    /// This lets us identify `let x = e; f(x)` with `f(e)`.
    /// Unmapped variables are assumed to be mutable (accessing them triggers a `Read` action)
    alias: HashMap<HirId, AnfValue<'tcx>>,
    span: Span,
}

fn a_normal_form<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    ((thir, expr), scope_tree): (&(Thir<'tcx>, ExprId), &ScopeTree),
    def_span: Span,
) -> Result<AnfFn<'tcx>, ErrorGuaranteed> {
    let mut ctx = AnfContext::new(ctx, thir, scope_tree, def_span);
    let mut stmts = Vec::new();
    let args = ctx.a_normal_form_args()?;
    let ret = ctx.a_normal_form_expr(*expr, &mut stmts)?;
    let span = ret.1;
    let body = AnfBlock { stmts, ret, span };
    Ok(AnfFn { args, body })
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for AnfContext<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}

impl<'a, 'tcx> AnfContext<'a, 'tcx> {
    fn new(
        ctx: &'a TranslationCtx<'tcx>,
        thir: &'a Thir<'tcx>,
        scope_tree: &'a ScopeTree,
        span: Span,
    ) -> Self {
        let alias = HashMap::new();
        AnfContext { ctx, thir, scope_tree, alias, span }
    }

    fn a_normal_form_args(&mut self) -> Result<Vec<AnfPattern>, ErrorGuaranteed> {
        self.thir
            .params
            .iter()
            .filter_map(|param| {
                let Some(pattern) = &param.pat else { return Some(Ok(AnfPattern::Wild)) };
                // We visit even ghost variables to record their (im)mutability.
                let pat = self.a_normal_form_pat(&pattern);
                if is_ghost_ty_(self.ctx.tcx, param.ty) {
                    return None;
                }
                Some(pat)
            })
            .collect()
    }

    fn a_normal_form_expr(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<(AnfValue<'tcx>, Span), ErrorGuaranteed> {
        let expr = &self.thir[expr_id];
        use ExprKind::*;
        let value = match &expr.kind {
            Scope { value, region_scope, .. } => {
                // Skip ghost blocks
                if let Some(hir_id) = region_scope.hir_id(self.scope_tree)
                    && is_ghost_block(self.tcx(), hir_id)
                {
                    AnfValue::Zst
                } else {
                    self.a_normal_form_expr(*value, stmts)?.0
                }
            }
            Block { block } => self.a_normal_form_block(*block, stmts)?,
            VarRef { id } => match self.alias.get(&id.0) {
                None => {
                    stmts.push(AnfStmt {
                        pattern: AnfPattern::Var(Var::ExprId(expr_id)),
                        rhs: AnfOp::by_value(
                            OpTag::Read,
                            [(
                                AnfValue::Borrow(AnfPlace::mut_var(Var::HirId(id.0)).into()),
                                expr.span,
                            )]
                            .into(),
                        ),
                        span: expr.span,
                    });
                    AnfValue::Var(Var::ExprId(expr_id))
                }
                Some(v) => v.clone(),
            },
            Call { fun, args, fn_span, .. } => {
                let fun = self.a_normal_form_expr(*fun, stmts)?;
                match fun.0 {
                    AnfValue::Fn(fun_id, subst) => {
                        let args = args
                            .iter()
                            .map(|arg| self.a_normal_form_expr(*arg, stmts))
                            .collect::<Result<::std::boxed::Box<[_]>, ErrorGuaranteed>>()?;
                        let (fun_id, subst, args) = if let Some(refined) = self.ctx.refines(fun_id)
                        {
                            let args = args
                                .into_iter()
                                .zip(&refined.erase_args)
                                .filter_map(|(arg, &erase)| if erase { None } else { Some(arg) })
                                .collect();
                            let subst = ty::EarlyBinder::bind(refined.thir.1)
                                .instantiate(self.tcx(), subst);
                            (refined.thir.0, subst, args)
                        } else {
                            (fun_id, subst, args)
                        };
                        stmts.push(AnfStmt {
                            pattern: AnfPattern::Var(Var::ExprId(expr_id)),
                            rhs: AnfOp::by_value(OpTag::Call(fun_id, subst), args),
                            span: *fn_span,
                        });
                        AnfValue::Var(Var::ExprId(expr_id))
                    }
                    _ => {
                        return Err(self
                            .error(self.span, "failed #[refines] check")
                            .with_span_label(fun.1, "unsupported function expression")
                            .emit());
                    }
                }
            }
            ZstLiteral { .. } => match expr.ty.kind() {
                ty::TyKind::FnDef(def_id, subst) => AnfValue::Fn(*def_id, subst),
                _ => AnfValue::Zst,
            },
            Binary { op, lhs, rhs } => {
                let lhs = self.a_normal_form_expr(*lhs, stmts)?;
                let rhs = self.a_normal_form_expr(*rhs, stmts)?;
                stmts.push(AnfStmt {
                    pattern: AnfPattern::Var(Var::ExprId(expr_id)),
                    rhs: AnfOp::by_value(OpTag::Binop(*op), [lhs, rhs].into()),
                    span: expr.span,
                });
                AnfValue::Var(Var::ExprId(expr_id))
            }
            Literal { lit, neg } => AnfValue::Literal(lit.node, *neg),
            ConstParam { param, .. } => AnfValue::Const(ty::Const::new_param(self.tcx(), *param)),
            Deref { arg } => {
                let arg = self.a_normal_form_expr(*arg, stmts)?;
                stmts.push(AnfStmt {
                    pattern: AnfPattern::Var(Var::ExprId(expr_id)),
                    rhs: AnfOp::by_value(OpTag::Deref, [arg].into()),
                    span: expr.span,
                });
                AnfValue::Var(Var::ExprId(expr_id))
            }
            // THIR inserts some &*, we simplify them
            Borrow { arg, .. } if let Deref { arg } = &self.thir[*arg].kind => {
                self.a_normal_form_expr(*arg, stmts)?.0
            }
            Borrow { arg, .. } => {
                let place = self.a_normal_form_place(*arg, stmts)?;
                AnfValue::Borrow(std::boxed::Box::new(place))
            }
            Tuple { fields } => {
                // Visit all fields even if they have type `Ghost<_>` because they may all have effects
                // It's just their values we may discard in the end.
                let values = fields
                    .iter()
                    .map(|f| self.a_normal_form_expr(*f, stmts))
                    .collect::<Result<::std::boxed::Box<[_]>, ErrorGuaranteed>>()?;
                if fields.len() >= 1
                    && fields.iter().skip(1).all(|e| is_ghost_ty_(self.tcx(), self.thir[*e].ty))
                {
                    // Erase ghost fields
                    values.into_iter().next().unwrap().0
                } else {
                    AnfValue::Ctor(Ctor::Tuple, values)
                }
            }
            _ => {
                return Err(self
                    .error(self.span, "failed #[refines] check")
                    .with_span_label(expr.span, format!("unsupported expression"))
                    .emit());
            }
        };
        Ok((value, expr.span))
    }

    fn a_normal_form_place(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<AnfPlace<'tcx>, ErrorGuaranteed> {
        let expr = &self.thir[expr_id];
        use ExprKind::*;
        match &expr.kind {
            VarRef { id } => match self.alias.get(&id.0) {
                None => Ok(AnfPlace::mut_var(Var::HirId(id.0))),
                Some(v) => Ok(AnfPlace::immut(v.clone())),
            },
            Deref { arg } => {
                let mut place = self.a_normal_form_place(*arg, stmts)?;
                place.add_deref();
                Ok(place)
            }
            Scope { value, .. } => self.a_normal_form_place(*value, stmts),
            _ => {
                let v = self.a_normal_form_expr(expr_id, stmts)?;
                if let AnfValue::Var(Var::ExprId(expr_id2)) = v.0
                    && expr_id2 == expr_id
                {
                    // expr_id was just bound so we can use it as a place
                    Ok(AnfPlace::mut_var(Var::ExprId(expr_id)))
                } else {
                    // we create a place for expr_id
                    stmts.push(AnfStmt {
                        pattern: AnfPattern::Var(Var::ExprId(expr_id)),
                        rhs: AnfOp::by_value(OpTag::Value, [v].into()),
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
            None => Ok(AnfValue::Zst),
            Some(e) => Ok(self.a_normal_form_expr(e, stmts)?.0),
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
                    return Err(self
                        .error(self.span, "failed #[refines] check")
                        .with_span_label(*span, "unsupported let-else")
                        .emit());
                }
                let Some(initializer) = initializer else {
                    return Err(self
                        .error(self.span, "failed #[refines] check")
                        .with_span_label(*span, "unsupported let without initializer")
                        .emit());
                };
                if is_spec_or_refines_expr(self.tcx(), self.thir, *initializer) {
                    return Ok(());
                }
                let rhs = self.a_normal_form_expr(*initializer, stmts)?;
                let mut pattern = &**pattern;
                loop {
                    match &pattern.kind {
                        PatKind::Binding {
                            var,
                            mode: BindingMode(ByRef::No, Mutability::Not),
                            subpattern: None,
                            ..
                        } => {
                            // Skip generating a binding
                            self.alias.insert(var.0, rhs.0.clone());
                            return Ok(());
                        }
                        PatKind::Leaf { subpatterns }
                            if subpatterns.len() >= 1
                                && subpatterns
                                    .iter()
                                    .skip(1)
                                    .all(|p| is_ghost_ty_(self.tcx(), p.pattern.ty)) =>
                        {
                            // Erase ghost fields
                            pattern = &subpatterns[0].pattern;
                        }
                        _ => break,
                    };
                }
                let lhs = self.a_normal_form_pat(&pattern)?;
                stmts.push(AnfStmt {
                    pattern: lhs,
                    rhs: AnfOp::by_value(OpTag::Value, [rhs].into()),
                    span: *span,
                });
            }
        }
        Ok(())
    }

    fn a_normal_form_pat(&mut self, pat: &thir::Pat<'tcx>) -> Result<AnfPattern, ErrorGuaranteed> {
        use PatKind::*;
        match &pat.kind {
            Wild => Ok(AnfPattern::Wild),
            Binding { var, mode: BindingMode(ByRef::No, Mutability::Not), .. } => {
                let v = Var::HirId(var.0);
                self.alias.insert(var.0, AnfValue::Var(v));
                Ok(AnfPattern::Var(v))
            }
            Binding { var, .. } => Ok(AnfPattern::Var(Var::HirId(var.0))),
            PatKind::Leaf { subpatterns } => {
                let subpatterns = subpatterns
                    .iter()
                    .map(|p| self.a_normal_form_pat(&p.pattern))
                    .collect::<Result<::std::boxed::Box<[_]>, ErrorGuaranteed>>()?;
                // the actual constructor doesn't matter for a `Leaf` so we just use `Tuple`
                Ok(AnfPattern::Ctor(Ctor::Tuple, subpatterns, pat.span))
            }
            _ => Err(self
                .error(self.span, "failed #[refines] check")
                .with_span_label(pat.span, "unsupported pattern")
                .emit()),
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
                return is_spec(tcx, closure_id) || is_refines(tcx, closure_id);
            }
            _ => return false,
        }
    }
}

struct RefineChecker<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    refine_var: HashMap<Var, Var>,
    left_span: Span,
    right_span: Span,
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for RefineChecker<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}

impl<'a, 'tcx> RefineChecker<'a, 'tcx> {
    fn new(ctx: &'a TranslationCtx<'tcx>, left_span: Span, right_span: Span) -> Self {
        let refine_var = HashMap::new();
        RefineChecker { ctx, refine_var, left_span, right_span }
    }

    fn refines_value(&self, v1: &AnfValue<'tcx>, v2: &AnfValue<'tcx>) -> bool {
        match (v1, v2) {
            (AnfValue::Zst, AnfValue::Zst) => true,
            (AnfValue::Var(v1), AnfValue::Var(v2)) => {
                let Some(v1_) = self.refine_var.get(v1) else { return false };
                v1_ == v2
            }
            (AnfValue::Literal(lit1, neg1), AnfValue::Literal(lit2, neg2)) => {
                lit1 == lit2 && neg1 == neg2
            }
            (AnfValue::Const(p1), AnfValue::Const(p2)) => p1 == p2,
            (AnfValue::Borrow(place1), AnfValue::Borrow(place2)) => {
                self.refines_place(place1, place2)
            }
            _ => false,
        }
    }

    fn refines_place(&self, p1: &AnfPlace<'tcx>, p2: &AnfPlace<'tcx>) -> bool {
        let refine_base = match (&p1.base, &p2.base) {
            (AnfPlaceBase::MutVar(v1), AnfPlaceBase::MutVar(v2)) => {
                let Some(v1_) = self.refine_var.get(v1) else { return false };
                v1_ == v2
            }
            (AnfPlaceBase::ImmutVar(v1), AnfPlaceBase::ImmutVar(v2)) => self.refines_value(v1, v2),
            _ => false,
        };
        refine_base && p1.projections == p2.projections
    }

    fn refines_pattern(
        &mut self,
        pat1: &AnfPattern,
        pat2: &AnfPattern,
    ) -> Result<(), ErrorGuaranteed> {
        match (pat1, pat2) {
            (AnfPattern::Var(v1), AnfPattern::Var(v2)) => {
                self.new_var(*v1, *v2);
            }
            (AnfPattern::Ctor(c1, args1, span1), AnfPattern::Ctor(c2, args2, span2)) => {
                if c1 == c2 {
                    for (a1, a2) in args1.into_iter().zip(args2.into_iter()) {
                        self.refines_pattern(a1, a2)?;
                    }
                } else {
                    return Err(self
                        .error(*span1, "failed #[refines] check")
                        .with_span_note(*span1, "#[refines] pattern")
                        .with_span_note(*span2, "refined pattern")
                        .emit());
                }
            }
            (AnfPattern::Wild, _) | (_, AnfPattern::Wild) => {}
            _ => {}
        }
        Ok(())
    }

    fn new_var(&mut self, v1: Var, v2: Var) {
        self.refine_var.insert(v1, v2);
    }

    fn refines_stmts(
        &mut self,
        left: &AnfBlock<'tcx>,
        right: &AnfBlock<'tcx>,
    ) -> Result<(), ErrorGuaranteed> {
        use std::cmp::Ordering::*;
        // We try to compare the two blocks as far as we can to get more precise errors in case of mismatch,
        // that's why we compare the lengths at the end.
        for (left, right) in left.stmts.iter().zip(&right.stmts) {
            let debug_string = |tag| {
                use OpTag::*;
                match tag {
                    Value => " (value)".into(),
                    Read => " (read)".into(),
                    Call(def_id, subst) => {
                        format!(" ({}{})", self.tcx().def_path_str(def_id), subst.print_as_list())
                    }
                    _ => "".into(),
                }
            };
            if left.rhs.tag != right.rhs.tag {
                return Err(self
                    .error(left.span, "failed #[refines] check")
                    .with_span_label(
                        left.span,
                        format!("#[refines] expression{}", debug_string(left.rhs.tag)),
                    )
                    .with_span_label(
                        right.span,
                        format!("refined expression{}", debug_string(right.rhs.tag)),
                    )
                    .emit());
            }
            assert!(left.rhs.args.len() == right.rhs.args.len());
            for (left, right) in left.rhs.args.iter().zip(&right.rhs.args) {
                if !self.refines_value(&left.0, &right.0) {
                    return Err(self
                        .error(left.1, "failed #[refines] check")
                        .with_span_label(left.1, "#[refines] expression")
                        .with_span_label(right.1, "refined expression")
                        .emit());
                }
            }
            for (left, right) in left.rhs.arms.iter().zip(&right.rhs.arms) {
                self.refines_pattern(&left.pattern, &right.pattern)?;
                self.refines_body(&left.body, &right.body)?;
            }
            match left.rhs.arms.len().cmp(&right.rhs.arms.len()) {
                Equal => {}
                Less => {
                    let right_span = right.rhs.arms[left.rhs.arms.len()].span;
                    return Err(self
                        .error(right_span, "failed #[refines] check")
                        .with_span_label(right_span, "refined block (mismatched block)")
                        .with_span_label(left.span, "#[refines] expression (no matching block)")
                        .emit());
                }
                Greater => {
                    let left_span = left.rhs.arms[right.rhs.arms.len()].span;
                    return Err(self
                        .error(left_span, "failed #[refines] check")
                        .with_span_label(left_span, "#[refines] block (mismatched block)")
                        .with_span_label(right.span, "refined expression (no matching block)")
                        .emit());
                }
            }
            self.refines_pattern(&left.pattern, &right.pattern)?;
        }
        match left.stmts.len().cmp(&right.stmts.len()) {
            Equal => {}
            Less => {
                let right_span = right.stmts[left.stmts.len()].span;
                return Err(self
                    .error(right_span, "failed #[refines] check")
                    .with_span_label(right_span, "refined block (mismatched statement)")
                    .with_span_label(left.span, "#[refines] block (no matching statement)")
                    .emit());
            }
            Greater => {
                let right_span = left.stmts[right.stmts.len()].span;
                return Err(self
                    .error(right_span, "failed #[refines] check")
                    .with_span_label(right_span, "#[refines] block (mismatched statement)")
                    .with_span_label(right.span, "refined block (no matching statement)")
                    .emit());
            }
        }
        Ok(())
    }

    fn refines_body(
        &mut self,
        left: &AnfBlock<'tcx>,
        right: &AnfBlock<'tcx>,
    ) -> Result<(), ErrorGuaranteed> {
        self.refines_stmts(left, right)?;
        if self.refines_value(&left.ret.0, &right.ret.0) {
            Ok(())
        } else {
            Err(self
                .error(left.ret.1, "failed #[refines] check")
                .with_span_label(left.ret.1, "#[refines] side (mismatched value)")
                .with_span_label(right.ret.1, "refined side")
                .emit())
        }
    }

    fn refines(&mut self, left: &AnfFn<'tcx>, right: &AnfFn<'tcx>) -> Result<(), ErrorGuaranteed> {
        use std::cmp::Ordering::*;
        match left.args.len().cmp(&right.args.len()) {
            Less => {
                return Err(self
                    .error(self.left_span, "failed #[refines] check")
                    .with_span_label(
                        self.left_span,
                        "#[refines] function has fewer non-ghost arguments than refined function",
                    )
                    .with_span_label(self.right_span, "refined function")
                    .emit());
            }
            Greater => {
                return Err(self
                    .error(self.left_span, "failed #[refines] check")
                    .with_span_label(
                        self.left_span,
                        "#[refines] function has more non-ghost arguments than refined function",
                    )
                    .with_span_label(self.right_span, "refined function")
                    .emit());
            }
            Equal => {}
        }
        for (left, right) in left.args.iter().zip(&right.args) {
            self.refines_pattern(left, right)?;
        }
        self.refines_body(&left.body, &right.body)
    }
}

fn check_refines_thir<'a, 'tcx>(
    ctx: &TranslationCtx<'tcx>,
    left: (&'a (Thir<'tcx>, ExprId), &'a ScopeTree),
    right: (&'a (Thir<'tcx>, ExprId), &'a ScopeTree),
    subst2: ty::GenericArgsRef<'tcx>,
    left_span: Span,
    right_span: Span,
) -> Result<(), ErrorGuaranteed> {
    let left = a_normal_form(ctx, left, left_span)?;
    // Even when processing `right_thir`, error messages should mention `left_span`:
    // the span of the function carrying the `#[refines]` attribute.
    let right = a_normal_form(ctx, right, left_span)?;
    let right = ty::EarlyBinder::bind(right).instantiate(ctx.tcx, subst2);
    let mut checker = RefineChecker::new(ctx, left_span, right_span);
    let r = checker.refines(&left, &right);
    if r.is_err() {
        debug!("{left:#?}\n{right:#?}");
    }
    r
}
