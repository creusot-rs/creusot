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

use rustc_abi::VariantIdx;
use rustc_ast::{BindingMode, ByRef, Mutability};
use rustc_hir::{
    HirId,
    def_id::{DefId, LocalDefId},
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    middle::region::ScopeTree,
    mir,
    thir::{self, AdtExpr, ArmId, BlockId, ExprId, ExprKind, PatKind, StmtId, Thir},
    ty::{self, TyCtxt, adjustment::PointerCoercion::MutToConstPointer},
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{ErrorGuaranteed, Span, SpanDecoder, SpanEncoder};

use crate::{
    backend::is_trusted_item,
    contracts_items::{is_ptr_own_as_mut, is_ptr_own_as_ref, is_refines, is_spec},
    ctx::{HasTyCtxt, TranslationCtx},
    util::{ODecodable, OEncodable},
    validate::{ghost::is_ghost_ty_, is_ghost_block},
};

pub(crate) fn validate_refines(ctx: &TranslationCtx) {
    // Only do the refines check for the primary package
    // to minimize the number of THIR bodies stored by dependencies
    if !ctx.opts.should_output {
        return;
    }
    let mut err = Ok(());
    for (left, right) in ctx.iter_refines_to_check() {
        err = err.and(check_refines(ctx, *left, *right));
    }
    // Write out the required THIR bodies before bailing out
    err.and(ctx.dump_thir_required()).unwrap_or_else(|e| e.raise_fatal())
}

fn check_refines<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    left: LocalDefId,
    (right, subst2): (DefId, ty::GenericArgsRef<'tcx>),
) -> Result<(), ErrorGuaranteed> {
    if is_trusted_item(ctx.tcx, left.to_def_id()) {
        return Ok(());
    }
    let left_span = ctx.def_span(left);
    let Some(left_thir) = ctx.get_local_thir(left) else {
        return Err(ctx.error(left_span, "#[refines] function must have a body").emit());
    };
    let right = match right.as_local() {
        None => match ctx.anf_thir(right) {
            None if ctx.opts.refines_check => {
                return Err(ctx
                    .error(
                        left_span,
                        format!("Missing body of {} for #[refines] check", ctx.def_path_str(right)),
                    )
                    .emit());
            }
            None => return Ok(()),
            Some(anf) => anf,
        },
        Some(right) => {
            let Some(right_thir) = ctx.get_local_thir(right) else {
                return Err(ctx
                    .error(ctx.def_span(right), "Refined function must have a body")
                    .emit());
            };
            let right_scope = ctx.tcx.region_scope_tree(right);
            // Even when processing `right_thir`, error messages should mention `refines_span`:
            // the span of the function carrying the `#[refines]` attribute.
            let right = a_normal_form(ctx, (right_thir, right_scope), left_span).map_err(|e| {
                debug!("{:#?}", right_thir);
                e
            })?;
            &ty::EarlyBinder::bind(right).instantiate(ctx.tcx, subst2)
        }
    };
    let left_scope = ctx.tcx.region_scope_tree(left);
    let left = a_normal_form(ctx, (left_thir, left_scope), left_span).map_err(|e| {
        debug!("{:#?}", left_thir);
        e
    })?;
    check_refines_thir(ctx, &left, right, left_span)
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable, TyEncodable, TyDecodable)]
pub(crate) struct AnfBlock<'tcx> {
    /// For `fn` arguments (as a `Ctor(Ctor::Tuple, _, _)`) and `match` patterns
    /// Otherwise `Wild`.
    pattern: AnfPattern,
    stmts: Vec<AnfStmt<'tcx>>,
    ret: (AnfValue<'tcx>, Span),
    span: Span,
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

impl<D: SpanDecoder> Decodable<D> for Var {
    fn decode(d: &mut D) -> Self {
        if d.read_bool() {
            Var::HirId(Decodable::decode(d))
        } else {
            Var::ExprId(ODecodable::odecode(d))
        }
    }
}

impl<E: SpanEncoder> Encodable<E> for Var {
    fn encode(&self, e: &mut E) {
        match self {
            Var::HirId(v) => {
                e.emit_bool(true);
                v.encode(e)
            }
            Var::ExprId(v) => {
                e.emit_bool(false);
                v.oencode(e)
            }
        }
    }
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable, TyEncodable, TyDecodable)]
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
/// We inline values into statements. That makes it easier to deal with case like this:
/// ```
/// f(1, g())
/// ```
/// in our ANF, that becomes:
/// ```
/// let x = g(); f(1, x)
/// ```
/// where `1` and `g()` swapped relative positions. Whereas if we stuck to a more conventional
/// definition of ANF, we would have to do extra work to equate
/// ```
/// let w = 1;
/// let x = g();
/// f(w, x)
/// ```
/// vs
/// ```
/// let x = g();
/// let w = 1
/// f(w, x)
/// ```
#[derive(Clone, Debug, TypeVisitable, TypeFoldable, TyEncodable, TyDecodable)]
struct AnfOp<'tcx> {
    tag: OpTag<'tcx>,
    args: Box<[(AnfValue<'tcx>, Span)]>,
    arms: Box<[AnfBlock<'tcx>]>,
}

/// Tag for `AnfOp`
#[derive(Clone, Copy, Debug, PartialEq, TypeVisitable, TypeFoldable, TyEncodable, TyDecodable)]
enum OpTag<'tcx> {
    Value,
    Deref,
    Read,
    BinOp(mir::BinOp),
    UnOp(mir::UnOp),
    LogicalOp(LogicalOp),
    Call(DefId, ty::GenericArgsRef<'tcx>),
    Const(DefId, ty::GenericArgsRef<'tcx>),
    /// Statement emitted when reborrowing a raw pointer
    UnsafeBorrow,
    Return,
    IfLet,
    If,
    Match,
    LetElse,
    Loop,
    /// `match` guards are represented by a `Guard` statement at the start of a block
    Guard,
}

impl<'tcx> AnfOp<'tcx> {
    fn by_value(tag: OpTag<'tcx>, args: Box<[(AnfValue<'tcx>, Span)]>) -> Self {
        Self { tag, args, arms: [].into() }
    }

    fn value(arg: (AnfValue<'tcx>, Span)) -> Self {
        Self::by_value(OpTag::Value, [arg].into())
    }

    fn deref(arg: (AnfValue<'tcx>, Span)) -> Self {
        Self::by_value(OpTag::Deref, [arg].into())
    }

    fn read(arg: (AnfValue<'tcx>, Span)) -> Self {
        Self::by_value(OpTag::Read, [arg].into())
    }

    fn binary(op: mir::BinOp, arg1: (AnfValue<'tcx>, Span), arg2: (AnfValue<'tcx>, Span)) -> Self {
        Self::by_value(OpTag::BinOp(op), [arg1, arg2].into())
    }

    fn unary(op: mir::UnOp, arg: (AnfValue<'tcx>, Span)) -> Self {
        Self::by_value(OpTag::UnOp(op), [arg].into())
    }

    fn call(
        fun_id: DefId,
        subst: ty::GenericArgsRef<'tcx>,
        args: Box<[(AnfValue<'tcx>, Span)]>,
    ) -> Self {
        Self::by_value(OpTag::Call(fun_id, subst), args)
    }

    fn const_(const_id: DefId, subst: ty::GenericArgsRef<'tcx>) -> Self {
        Self::by_value(OpTag::Const(const_id, subst), [].into())
    }

    fn return_(res: Option<(AnfValue<'tcx>, Span)>) -> Self {
        Self::by_value(OpTag::Return, res.into_iter().collect())
    }

    fn unsafe_borrow(bor: (AnfValue<'tcx>, Span)) -> Self {
        Self::by_value(OpTag::UnsafeBorrow, [bor].into())
    }

    /// The body of the `if let` is ANF-ed into preceding statements:
    /// `if let pat = f(x)` -> `if let y = f(x) && let pat = y`
    fn iflet(val: (AnfValue<'tcx>, Span)) -> Self {
        Self::by_value(OpTag::IfLet, [val].into())
    }

    fn control(
        tag: OpTag<'tcx>,
        args: Box<[(AnfValue<'tcx>, Span)]>,
        arms: Box<[AnfBlock<'tcx>]>,
    ) -> Self {
        Self { tag, args, arms }
    }

    /// `cond` is a block instead of a ANF value because it may contain `if let`
    /// which has special semantics
    fn if_(cond: AnfBlock<'tcx>, then: AnfBlock<'tcx>, else_: Option<AnfBlock<'tcx>>) -> Self {
        let arms = match else_ {
            None => [cond, then].into(),
            Some(else_) => [cond, then, else_].into(),
        };
        Self::control(OpTag::If, [].into(), arms)
    }

    fn logicalop(op: thir::LogicalOp, lhs: AnfBlock<'tcx>, rhs: AnfBlock<'tcx>) -> Self {
        Self::control(op.into(), [].into(), [lhs, rhs].into())
    }

    fn loop_(body: AnfBlock<'tcx>) -> Self {
        Self::control(OpTag::Loop, [].into(), [body].into())
    }

    fn match_(scrutinee: (AnfValue<'tcx>, Span), arms: Box<[AnfBlock<'tcx>]>) -> Self {
        Self::control(OpTag::Match, [scrutinee].into(), arms)
    }

    fn guard(cond: AnfBlock<'tcx>) -> Self {
        Self::control(OpTag::Guard, [].into(), [cond].into())
    }

    fn letelse(val: (AnfValue<'tcx>, Span), else_: AnfBlock<'tcx>) -> Self {
        Self::control(OpTag::LetElse, [val].into(), [else_].into())
    }
}

#[derive(Clone, Debug, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
enum AnfPattern {
    Wild,
    Var(Var),
    Ctor(Ctor, Box<[AnfPattern]>, Span),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
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
    Ctor(Ctor, Box<[(AnfValue<'tcx>, Span)]>),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
enum Ctor {
    Adt(DefId, VariantIdx),
    Tuple,
    Array,
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
struct AnfPlace<'tcx> {
    base: AnfPlaceBase<'tcx>,
    projections: Vec<AnfProjection>,
}

impl<'tcx> AnfPlace<'tcx> {
    fn is_unsafe(&self) -> bool {
        self.projections.iter().any(|proj| proj.is_unsafe())
    }

    /// If this is a reborrow of a borrow, simplify it to the original borrow
    fn borrow(self) -> AnfValue<'tcx> {
        if matches!(&self.projections[..], [AnfProjection::Deref { unsafe_: false }])
            && let AnfPlaceBase::ImmutVar(v) = self.base
        {
            v
        } else {
            AnfValue::Borrow(Box::new(self))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
enum AnfProjection {
    Deref { unsafe_: bool },
}

impl AnfProjection {
    fn is_unsafe(&self) -> bool {
        use AnfProjection::*;
        match self {
            Deref { unsafe_ } => *unsafe_,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
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

    fn add_deref(&mut self, unsafe_: bool) {
        self.projections.push(AnfProjection::Deref { unsafe_ });
    }
}

impl<'tcx> From<thir::LogicalOp> for OpTag<'tcx> {
    fn from(op: thir::LogicalOp) -> Self {
        OpTag::LogicalOp(LogicalOp(op))
    }
}

/// `thir::LogicalOp` does not implement `PartialEq`...
#[derive(Debug, Clone, Copy, TypeVisitable, TypeFoldable)]
struct LogicalOp(
    #[type_visitable(ignore)]
    #[type_foldable(identity)]
    thir::LogicalOp,
);

impl PartialEq<LogicalOp> for LogicalOp {
    fn eq(&self, rhs: &Self) -> bool {
        use thir::LogicalOp::*;
        match (self.0, rhs.0) {
            (And, And) | (Or, Or) => true,
            _ => false,
        }
    }
}

impl Eq for LogicalOp {}

impl<E: Encoder> Encodable<E> for LogicalOp {
    fn encode(&self, e: &mut E) {
        use thir::LogicalOp::*;
        e.emit_bool(match self.0 {
            And => true,
            Or => false,
        })
    }
}

impl<D: Decoder> Decodable<D> for LogicalOp {
    fn decode(d: &mut D) -> Self {
        use thir::LogicalOp::*;
        Self(if d.read_bool() { And } else { Or })
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
) -> Result<AnfBlock<'tcx>, ErrorGuaranteed> {
    let mut ctx = AnfContext::new(ctx, thir, scope_tree, def_span);
    let pattern = ctx.a_normal_form_args()?;
    ctx.a_normal_form_expr_block_(*expr, pattern, Vec::new(), None)
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

    fn a_normal_form_args(&mut self) -> Result<AnfPattern, ErrorGuaranteed> {
        let args = self
            .thir
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
            .collect::<Result<Box<[_]>, _>>()?;
        Ok(AnfPattern::Ctor(Ctor::Tuple, args, self.span))
    }

    fn a_normal_form_expr(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<(AnfValue<'tcx>, Span), ErrorGuaranteed> {
        let expr = &self.thir[expr_id];
        let bind_var = |stmts: &mut Vec<AnfStmt<'tcx>>, rhs| {
            stmts.push(AnfStmt {
                pattern: AnfPattern::Var(Var::ExprId(expr_id)),
                rhs,
                span: expr.span,
            });
            AnfValue::Var(Var::ExprId(expr_id))
        };
        use ExprKind::*;
        let value = match &expr.kind {
            Scope { value, region_scope, .. } => {
                // Skip ghost blocks
                if let Some(hir_id) = region_scope.hir_id(self.scope_tree)
                    && is_ghost_block(self.tcx(), hir_id)
                {
                    AnfValue::Unit
                } else {
                    self.a_normal_form_expr(*value, stmts)?.0
                }
            }
            Block { block } => self.a_normal_form_block(*block, stmts)?,
            VarRef { id } => match self.alias.get(&id.0) {
                None => bind_var(
                    stmts,
                    AnfOp::read((
                        AnfValue::Borrow(AnfPlace::mut_var(Var::HirId(id.0)).into()),
                        expr.span,
                    )),
                ),
                Some(v) => v.clone(),
            },
            Call { fun, args, .. } => {
                let fun = self.a_normal_form_expr(*fun, stmts)?;
                match fun.0 {
                    AnfValue::Fn(fun_id, subst) => 'fun: {
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
                            let subst =
                                ty::EarlyBinder::bind(refined.def.1).instantiate(self.tcx(), subst);
                            (refined.def.0, subst, args)
                        } else if is_ptr_own_as_ref(self.tcx(), fun_id)
                            || is_ptr_own_as_mut(self.tcx(), fun_id)
                        {
                            let arg0 = args.into_iter().next().unwrap();
                            let mut place = std::boxed::Box::new(AnfPlace::immut(arg0.0));
                            place.add_deref(true); // Add unsafe deref
                            break 'fun bind_var(
                                stmts,
                                AnfOp::unsafe_borrow((AnfValue::Borrow(place), arg0.1)),
                            );
                        } else {
                            (fun_id, subst, args)
                        };
                        bind_var(stmts, AnfOp::call(fun_id, subst, args))
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
                _ => AnfValue::Unit,
            },
            Binary { op, lhs, rhs } => {
                let lhs = self.a_normal_form_expr(*lhs, stmts)?;
                let rhs = self.a_normal_form_expr(*rhs, stmts)?;
                bind_var(stmts, AnfOp::binary(*op, lhs, rhs))
            }
            Unary { op, arg } => {
                let arg = self.a_normal_form_expr(*arg, stmts)?;
                bind_var(stmts, AnfOp::unary(*op, arg))
            }
            LogicalOp { op, lhs, rhs } => {
                let lhs = self.a_normal_form_expr_block(*lhs)?;
                let rhs = self.a_normal_form_expr_block(*rhs)?;
                bind_var(stmts, AnfOp::logicalop(*op, lhs, rhs))
            }
            Literal { lit, neg } => AnfValue::Literal(lit.node, *neg),
            ConstParam { param, .. } => AnfValue::Const(ty::Const::new_param(self.tcx(), *param)),
            Deref { arg } => {
                let arg = self.a_normal_form_expr(*arg, stmts)?;
                bind_var(stmts, AnfOp::deref(arg))
            }
            // THIR inserts some &*, we simplify them
            Borrow { arg, .. } if let Deref { arg } = &self.thir[*arg].kind => {
                self.a_normal_form_expr(*arg, stmts)?.0
            }
            Borrow { arg, .. } => {
                let place = self.a_normal_form_place(*arg, stmts)?;
                if place.is_unsafe() {
                    let bor = AnfValue::Borrow(std::boxed::Box::new(place));
                    bind_var(stmts, AnfOp::unsafe_borrow((bor, self.thir[*arg].span)))
                } else {
                    place.borrow()
                }
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
            If { cond, then, else_opt, .. } => {
                let cond = self.a_normal_form_expr_block(*cond)?;
                let then = self.a_normal_form_expr_block(*then)?;
                let else_ =
                    else_opt.map(|else_| self.a_normal_form_expr_block(else_)).transpose()?;
                bind_var(stmts, AnfOp::if_(cond, then, else_))
            }
            Return { value } => {
                let value = value.map(|value| self.a_normal_form_expr(value, stmts)).transpose()?;
                stmts.push(AnfStmt {
                    pattern: AnfPattern::Wild,
                    rhs: AnfOp::return_(value),
                    span: expr.span,
                });
                AnfValue::Unit
            }
            NeverToAny { source } => return self.a_normal_form_expr(*source, stmts),
            Loop { body } => {
                let body = self.a_normal_form_expr_block(*body)?;
                bind_var(stmts, AnfOp::loop_(body))
            }
            Let { pat, expr: body } => {
                let val = self.a_normal_form_expr(*body, stmts)?;
                let pattern = self.a_normal_form_pat(&pat)?;
                stmts.push(AnfStmt { pattern, rhs: AnfOp::iflet(val), span: expr.span });
                AnfValue::Unit
            }
            Match { scrutinee, arms, .. } => {
                let scrutinee = self.a_normal_form_expr(*scrutinee, stmts)?;
                let arms = arms
                    .iter()
                    .map(|arm| self.a_normal_form_arm(*arm))
                    .collect::<Result<_, _>>()?;
                bind_var(stmts, AnfOp::match_(scrutinee, arms))
            }
            Array { fields } => {
                let fields = fields
                    .iter()
                    .map(|field_id| self.a_normal_form_expr(*field_id, stmts))
                    .collect::<Result<_, _>>()?;
                AnfValue::Ctor(Ctor::Array, fields)
            }
            Adt(box AdtExpr { adt_def, variant_index, fields, .. }) => {
                let fields = fields
                    .iter()
                    .map(|field| self.a_normal_form_expr(field.expr, stmts))
                    .collect::<Result<_, _>>()?;
                AnfValue::Ctor(Ctor::Adt(adt_def.did(), *variant_index), fields)
            }
            NamedConst { def_id, args, .. } => bind_var(stmts, AnfOp::const_(*def_id, args)),
            PointerCoercion { cast: MutToConstPointer, source, .. } => {
                self.a_normal_form_expr(*source, stmts)?.0
            }
            kind => {
                return Err(self
                    .error(self.span, "failed #[refines] check")
                    .with_span_label(expr.span, format!("unsupported expression"))
                    .with_note(format!("unsupported: {kind:?}"))
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
                let unsafe_ = match self.thir[*arg].ty.kind() {
                    ty::TyKind::Ref(_, _, _) => false,
                    _ => true, // RawPtr
                };
                let mut place = self.a_normal_form_place(*arg, stmts)?;
                place.add_deref(unsafe_);
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
                        rhs: AnfOp::value(v),
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
            Some(e) => Ok(self.a_normal_form_expr(e, stmts)?.0),
        }
    }

    fn a_normal_form_expr_block(
        &mut self,
        expr_id: ExprId,
    ) -> Result<AnfBlock<'tcx>, ErrorGuaranteed> {
        self.a_normal_form_expr_block_(expr_id, AnfPattern::Wild, Vec::new(), None)
    }

    fn a_normal_form_expr_block_(
        &mut self,
        expr_id: ExprId,
        pattern: AnfPattern,
        mut stmts: Vec<AnfStmt<'tcx>>,
        span: Option<Span>,
    ) -> Result<AnfBlock<'tcx>, ErrorGuaranteed> {
        let ret = self.a_normal_form_expr(expr_id, &mut stmts)?;
        let span = span.unwrap_or(ret.1);
        Ok(AnfBlock { pattern, stmts, ret, span })
    }

    fn a_normal_form_arm(&mut self, arm_id: ArmId) -> Result<AnfBlock<'tcx>, ErrorGuaranteed> {
        let arm = &self.thir[arm_id];
        let pattern = self.a_normal_form_pat(&arm.pattern)?;
        let stmts = match &arm.guard {
            Some(guard) => {
                let guard = self.a_normal_form_expr_block(*guard)?;
                vec![AnfStmt {
                    pattern: AnfPattern::Wild,
                    rhs: AnfOp::guard(guard),
                    span: arm.span,
                }]
            }
            None => Vec::new(),
        };
        self.a_normal_form_expr_block_(arm.body, pattern, stmts, Some(arm.span))
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
                let rhs = match else_block {
                    None => AnfOp::value(rhs),
                    Some(else_) => {
                        let mut stmts = Vec::new();
                        let val = self.a_normal_form_block(*else_, &mut stmts)?;
                        let span = self.thir[*else_].span;
                        AnfOp::letelse(
                            rhs,
                            AnfBlock { pattern: AnfPattern::Wild, stmts, ret: (val, span), span },
                        )
                    }
                };
                let lhs = self.a_normal_form_pat(&pattern)?;
                stmts.push(AnfStmt { pattern: lhs, rhs, span: *span });
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
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for RefineChecker<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}

impl<'a, 'tcx> RefineChecker<'a, 'tcx> {
    fn new(ctx: &'a TranslationCtx<'tcx>) -> Self {
        let refine_var = HashMap::new();
        RefineChecker { ctx, refine_var }
    }

    fn refines_value(&self, v1: &AnfValue<'tcx>, v2: &AnfValue<'tcx>) -> bool {
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
        left: &[AnfStmt<'tcx>],
        right: &[AnfStmt<'tcx>],
        left_span: Span,
        right_span: Span,
    ) -> Result<(), ErrorGuaranteed> {
        use std::cmp::Ordering::*;
        // We try to compare the two blocks as far as we can to get more precise errors in case of mismatch,
        // that's why we compare the lengths at the end.
        for (left, right) in left.iter().zip(right) {
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
            if left.rhs.tag != right.rhs.tag || left.rhs.args.len() != right.rhs.args.len() {
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
                self.refines(left, right)?;
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
        match left.len().cmp(&right.len()) {
            Equal => {}
            Less => {
                let right_span = right[left.len()].span;
                return Err(self
                    .error(right_span, "failed #[refines] check")
                    .with_span_label(right_span, "refined block (mismatched statement)")
                    .with_span_label(left_span, "#[refines] block (no matching statement)")
                    .emit());
            }
            Greater => {
                let left_span = left[right.len()].span;
                return Err(self
                    .error(left_span, "failed #[refines] check")
                    .with_span_label(left_span, "#[refines] block (mismatched statement)")
                    .with_span_label(right_span, "refined block (no matching statement)")
                    .emit());
            }
        }
        Ok(())
    }

    fn refines(
        &mut self,
        left: &AnfBlock<'tcx>,
        right: &AnfBlock<'tcx>,
    ) -> Result<(), ErrorGuaranteed> {
        self.refines_pattern(&left.pattern, &right.pattern)?;
        self.refines_stmts(&left.stmts, &right.stmts, left.span, right.span)?;
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
}

fn check_refines_thir<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    left: &AnfBlock<'tcx>,
    right: &AnfBlock<'tcx>,
    refines_span: Span,
) -> Result<(), ErrorGuaranteed> {
    let mut checker = RefineChecker::new(ctx);
    let r = checker.refines(&left, &right);
    if r.is_err() {
        debug!("{left:#?}\n{right:#?}");
    }
    r
}
