//! The `#[erasure]` check
//!
//! The main challenge is to equate
//! ```ignore
//! g(f(x))
//! ```
//! and
//! ```ignore
//! let y = f(x);
//! g(y)
//! ```
//! (We often expand expressions like that to insert `ghost!` blocks.)
//!
//! We solve that by transforming THIR expressions to A-normal form.
use std::{borrow::Cow, collections::HashMap, fmt::Formatter};

use creusot_args::options::ErasureCheck;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::{BindingMode, ByRef, Mutability};
use rustc_errors::{Diag, DiagMessage, SubdiagMessage};
use rustc_hir::{
    ItemLocalId,
    def_id::{DefId, LocalDefId},
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    middle::region::{Scope, ScopeTree},
    mir,
    thir::{self, AdtExpr, ArmId, BlockId, ExprId, ExprKind, PatKind, StmtId, Thir},
    ty::{self, TyCtxt, adjustment::PointerCoercion::MutToConstPointer},
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{DUMMY_SP, Span, SpanDecoder, SpanEncoder};
use rustc_type_ir::{Interner, VisitorResult as _};

use crate::{
    backend::is_trusted_item,
    contracts_items::{Intrinsic, is_before_loop, is_erasure, is_spec},
    ctx::{Erasure, HasTyCtxt, ThirExpr, TranslationCtx},
    translation::traits::TraitResolved,
    util::{NamelessGenericArgs, ODecodable, OEncodable},
    validate::{is_ghost_block, is_ghost_or_snap},
};

// * Top-level implementation

pub(crate) fn validate_erasures(ctx: &TranslationCtx) {
    // Only do the erasure check for the primary package
    // to minimize the number of THIR bodies stored by dependencies
    if !ctx.opts.should_output || ctx.opts.erasure_check.is_no() {
        return;
    }
    let mut err = Ok(());
    for (left, right) in ctx.iter_erasures_to_check() {
        err = match (err, check_erasure(ctx, *left, right)) {
            (_, Ok(())) => err,
            (Ok(()), Err(e)) => Err(e),
            (Err(e1), Err(e2)) => Err(e1.max(e2)),
        }
    }
    // If an error was raised (`Err(None)`), the compiler will stop at the next `abort_if_errors` call
    match err {
        Ok(()) | Err(None) => {}
        Err(Some(MissingBody)) => {
            ctx.warn(DUMMY_SP, "Some cross-crate `#[erasure]` checks were skipped.");
        }
    }
    // Refresh the list of erasures for this crate
    ctx.write_erasure_required();
}

/// Missing ANF THIR body from another crate
/// Note: we use `max` to merge `Option<MissingBody>` errors.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MissingBody;

/// Check that the erasure of `left_local`'s body is equal to `right`.
/// If `right` comes from an external crate, its body may or may not be available
/// so we are more lenient about errors in that case.
fn check_erasure<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    left_local: LocalDefId,
    right: &Erasure<'tcx>,
) -> Result<(), Option<MissingBody>> {
    let left = left_local.to_def_id();
    if is_trusted_item(ctx.tcx, left) {
        return Ok(());
    }
    let left_span = ctx.def_span(left_local);
    if ctx.tcx.hir_node_by_def_id(left_local).associated_body().is_none() {
        ctx.error(left_span, "#[erasure] function must have a body").emit();
        return Err(None);
    }
    let left_thir = ctx.thir_body(left_local);
    let left = a_normal_form_or_error(ctx, left_local, left_thir).ok_or_else(|| {
        debug!("{:#?}", left_thir);
        None
    })?;
    let level = if right.def.0.is_local() {
        // intra-crate erasure checks are always errors
        rustc_errors::Level::Error
    } else {
        // cross-crate erasure checks require a bit of set up so they are warnings by default
        erasure_check_level(ctx.opts.erasure_check)
    };
    let right_anf = match right.def.0.as_local() {
        None => match ctx.erased_thir(right.def.0) {
            None if ctx.opts.erasure_check.is_error() => {
                ctx.error(
                    left_span,
                    format!("Missing body of #[erasure] target {}", ctx.def_path_str(right.def.0)),
                )
                .emit();
                return Err(None);
            }
            None => return Err(Some(MissingBody)),
            Some(anf) => Cow::Borrowed(anf),
        },
        Some(right_local) => {
            if ctx.tcx.hir_node_by_def_id(right_local).associated_body().is_none() {
                ctx.error(left_span, "#[erasure] target must have a body").emit();
                return Err(None);
            }
            let right_thir = ctx.thir_body(right_local);
            let anf = a_normal_form_or_error(ctx, right_local, right_thir).ok_or_else(|| {
                debug!("{:#?}", right_thir);
                None
            })?;
            Cow::Owned(anf)
        }
    };
    let right = &ty::EarlyBinder::bind(right_anf.into_owned()).instantiate(ctx.tcx, right.def.1);
    Ok(equate_anf(ctx, left_local, &left, right, level).map_err(|_| None)?)
}

/// Equate two ANF bodies.
fn equate_anf<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    left_id: LocalDefId,
    left: &AnfBlock<'tcx>,
    right: &AnfBlock<'tcx>,
    level: rustc_errors::Level,
) -> Result<(), ()> {
    let mut checker = EqualityChecker::new(ctx.tcx, left_id, level);
    let r = checker.equate(&left, &right);
    if r.is_err() {
        let tcx = ctx.tcx;
        debug!("Left:\n{:#?}", Pretty { tcx, owner: Some(left_id), body: left });
        debug!("Right:\n{:#?}", Pretty { tcx, owner: None, body: right });
    }
    r
}

fn erasure_check_level(erasure_check: ErasureCheck) -> rustc_errors::Level {
    if erasure_check.is_error() { rustc_errors::Level::Error } else { rustc_errors::Level::Warning }
}

fn warn_or_error<'tcx>(
    tcx: TyCtxt<'tcx>,
    level: rustc_errors::Level,
    span: Span,
    msg: impl Into<DiagMessage>,
) -> Diag<'tcx, ()> {
    Diag::<()>::new(tcx.dcx(), level, msg).with_span(span)
}

// * ANF expressions

#[derive(Clone, Debug, TypeVisitable, TypeFoldable, TyEncodable, TyDecodable)]
pub(crate) struct AnfBlock<'tcx> {
    /// Labels for `break` (`'label: { ... }` and `'label: loop { ... }`)
    #[type_visitable(ignore)]
    #[type_foldable(identity)]
    label: Option<Scope>,
    /// For `fn` arguments (as a `Ctor(Ctor::Tuple, _, _)`) and `match` patterns
    /// Otherwise `Wild`.
    pattern: AnfPattern,
    stmts: Vec<AnfStmt<'tcx>>,
    ret: (AnfValue<'tcx>, Span),
    span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Var {
    /// Only the `local_id` component of a `HirId` can go through cross-crate serialization
    /// We throw away the `owner` which should be the enclosing function anyway.
    HirId(ItemLocalId),
    ExprId(ExprId),
}

impl<I: Interner> ty::TypeVisitable<I> for Var {
    fn visit_with<V: ty::TypeVisitor<I>>(&self, _: &mut V) -> V::Result {
        V::Result::output()
    }
}

impl<I: Interner> ty::TypeFoldable<I> for Var {
    fn fold_with<F: ty::TypeFolder<I>>(self, _: &mut F) -> Self {
        self
    }

    fn try_fold_with<F: ty::FallibleTypeFolder<I>>(self, _: &mut F) -> Result<Self, F::Error> {
        Ok(self)
    }
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
/// This makes the erasure check almost trivial: compare the tags, then compare the fields.
/// For example an addition would be represented as `GenericOp(Binop(Add), box [lhs, rhs], box [])`.
///
/// The second field contains by-value operands (arguments of function calls, binary operators,
/// `if` and `match` scrutinees, assignment lvalues and rvalues).
///
/// The third field contains sub-blocks of control structures (`if`, `match`, `let-else`).
/// For constructs other than `match`, the arms have their `pattern` field default to `Wild`.
///
/// We inline values into statements. That makes it easier to deal with case like this:
/// ```ignore
/// f(1, g())
/// ```
/// in our ANF, that becomes:
/// ```ignore
/// let x = g(); f(1, x)
/// ```
/// where `1` and `g()` swapped relative positions. Whereas if we stuck to a more conventional
/// definition of ANF, we would have to do extra work to equate
/// ```ignore
/// let w = 1;
/// let x = g();
/// f(w, x)
/// ```
/// vs
/// ```ignore
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
    Call(DefId, NamelessGenericArgs<'tcx>),
    Const(DefId, NamelessGenericArgs<'tcx>),
    /// Statement emitted when reborrowing a raw pointer
    UnsafeBorrow,
    Return,
    Break,
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
        subst: NamelessGenericArgs<'tcx>,
        args: Box<[(AnfValue<'tcx>, Span)]>,
    ) -> Self {
        Self::by_value(OpTag::Call(fun_id, subst), args)
    }

    fn const_(const_id: DefId, subst: ty::GenericArgsRef<'tcx>) -> Self {
        Self::by_value(OpTag::Const(const_id, subst.into()), [].into())
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

    fn break_(label: (AnfValue<'tcx>, Span), value: Option<(AnfValue<'tcx>, Span)>) -> Self {
        Self::by_value(
            OpTag::Break,
            match value {
                None => [label].into(),
                Some(value) => [label, value].into(),
            },
        )
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
    Deref(Box<AnfPattern>),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
enum AnfValue<'tcx> {
    Unit,
    Var(Var),
    Fn(DefId, NamelessGenericArgs<'tcx>),
    Literal(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        rustc_ast::LitKind,
        bool,
    ),
    Const(ty::Const<'tcx>),
    Borrow(Box<AnfPlace<'tcx>>),
    RawBorrow(Box<AnfPlace<'tcx>>),
    Ctor(Ctor, Box<[(AnfValue<'tcx>, Span)]>),
    Field(VariantIdx, FieldIdx, Box<AnfValue<'tcx>>),
    /// Cast from *[T] to *T
    Thin(Box<AnfValue<'tcx>>),
    /// Other casts
    Cast(ty::Ty<'tcx>, ty::Ty<'tcx>, Box<AnfValue<'tcx>>),
    /// Labels for `break` are represented as values too
    Label(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        Scope,
    ),
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
enum Ctor {
    Adt(DefId, VariantIdx),
    Bool(bool),
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

    fn raw_borrow(self) -> AnfValue<'tcx> {
        AnfValue::RawBorrow(Box::new(self))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, TypeVisitable, TypeFoldable, TyDecodable, TyEncodable)]
enum AnfProjection {
    Deref { unsafe_: bool },
    Field { variant: VariantIdx, field: FieldIdx },
}

impl AnfProjection {
    fn is_unsafe(&self) -> bool {
        use AnfProjection::*;
        match self {
            Deref { unsafe_ } => *unsafe_,
            Field { .. } => false,
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

    fn field(mut self, variant: VariantIdx, field: FieldIdx) -> Self {
        self.projections.push(AnfProjection::Field { variant, field });
        self
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

////////////////////////////////////////////////////////////////
// * ANF conversion
////////////////////////////////////////////////////////////////

/// Convert a THIR expression to ANF, erroring if the conversion fails.
/// This is used for intra-crate erasure checks, where we always have access to bodies.
fn a_normal_form_or_error<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: LocalDefId,
    thir: ThirExpr<'tcx>,
) -> Option<AnfBlock<'tcx>> {
    a_normal_form_(ctx.tcx, Some(ctx), def_id, thir, rustc_errors::Level::Error)
}

/// Convert a THIR expression to ANF, using the `--erasure-check` option to set the error or warning level.
/// This is used for ANF to be exported to another crate, so that by default (warn level) you don't get errors
/// depending on whether the user recompiled their project.
pub fn a_normal_form_for_export<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: LocalDefId,
    thir: ThirExpr<'tcx>,
) -> Option<AnfBlock<'tcx>> {
    let level = erasure_check_level(ctx.opts.erasure_check);
    a_normal_form_(ctx.tcx, Some(ctx), def_id, thir, level)
}

/// Convert a THIR expression to ANF, without access to `TranslationCtx`.
/// This is used in crates that don't depend on `creusot-contracts`.
pub fn a_normal_form_without_specs<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    erasure_check: ErasureCheck,
) -> Option<AnfBlock<'tcx>> {
    let level = erasure_check_level(erasure_check);
    if tcx.hir_node_by_def_id(def_id).associated_body().is_none() {
        warn_or_error(tcx, level, tcx.def_span(def_id), "#[erasure] target must have a body")
            .emit();
        return None;
    }
    let thir = tcx.thir_body(def_id).unwrap_or_else(|err| err.raise_fatal());
    a_normal_form_(tcx, None, def_id, thir, level)
}

/// This is the implementation shared by the variants above.
fn a_normal_form_<'tcx>(
    tcx: TyCtxt<'tcx>,
    ctx: Option<&TranslationCtx<'tcx>>,
    def_id: LocalDefId,
    (thir, expr): ThirExpr<'tcx>,
    level: rustc_errors::Level,
) -> Option<AnfBlock<'tcx>> {
    let thir = thir.borrow();
    let mut ctx = AnfBuilder::new(tcx, ctx, def_id, &thir, level);
    let pattern = ctx.a_normal_form_args().ok()?;
    ctx.a_normal_form_expr_block_(expr, pattern, Vec::new(), None).ok()
}

/// State for computing A-normal form
struct AnfBuilder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ctx: Option<&'a TranslationCtx<'tcx>>,
    def_id: LocalDefId,
    typing_env: ty::TypingEnv<'tcx>,
    thir: &'a Thir<'tcx>,
    scope_tree: &'a ScopeTree,
    /// Mapping from ANF variables to values
    /// This lets us identify `let x = e; f(x)` with `f(e)`.
    /// Variables can also be `Mutable`, and accessing them triggers a `Read` action.
    /// Unmapped variables are ghost variables, which erase to ().
    alias: HashMap<ItemLocalId, VarValue<'tcx>>,
    /// Warning or Error
    level: rustc_errors::Level,
}

enum VarValue<'tcx> {
    Value(AnfValue<'tcx>),
    Mutable,
}

// Note: most methods return `Result<_, ()>` instead of `Option<_>`
// to distinguish "an error happened" (`Err(())`) vs
// "there is nothing here (and that's fine)" (`None`).
// This also lets us use `Option::transpose` to map over `Option` faillibly.
impl<'a, 'tcx> AnfBuilder<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        ctx: Option<&'a TranslationCtx<'tcx>>,
        def_id: LocalDefId,
        thir: &'a Thir<'tcx>,
        level: rustc_errors::Level,
    ) -> Self {
        let alias = HashMap::new();
        let scope_tree = tcx.region_scope_tree(def_id);
        let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
        AnfBuilder { tcx, ctx, def_id, typing_env, thir, scope_tree, alias, level }
    }

    fn span(&self) -> Span {
        self.tcx.def_span(self.def_id)
    }

    fn unsupported_syntax_(
        &self,
        span: Span,
        msg: impl Into<SubdiagMessage>,
        note: Option<String>,
    ) {
        let diag = warn_or_error(
            self.tcx,
            self.level,
            span,
            format!(
                "unsupported syntax for #[erasure] check in {}",
                self.tcx.def_path_str(self.def_id)
            ),
        )
        .with_span_label(span, msg);
        let diag = match note {
            None => diag,
            Some(note) => diag.with_note(note),
        };
        diag.emit();
    }

    fn unsupported_syntax(&self, span: Span, msg: impl Into<SubdiagMessage>) {
        self.unsupported_syntax_(span, msg, None)
    }

    fn unsupported_syntax_with_note(
        &self,
        span: Span,
        msg: impl Into<SubdiagMessage>,
        note: String,
    ) {
        self.unsupported_syntax_(span, msg, Some(note))
    }

    fn a_normal_form_args(&mut self) -> Result<AnfPattern, ()> {
        let args = self
            .thir
            .params
            .iter()
            .filter_map(|param| {
                let Some(pattern) = &param.pat else { return Some(Ok(AnfPattern::Wild)) };
                // We visit even ghost variables to record their (im)mutability.
                let pat = self.a_normal_form_pat(&pattern);
                if is_ghost_or_snap(self.tcx, param.ty) {
                    return None;
                }
                Some(pat)
            })
            .collect::<Result<Box<[_]>, _>>()?;
        Ok(AnfPattern::Ctor(Ctor::Tuple, args, self.span()))
    }

    fn a_normal_form_expr(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<(AnfValue<'tcx>, Span), ()> {
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
            // Loop labels are encoded via Scope { value: Loop {} }
            Scope { value, region_scope, .. } => {
                // Skip ghost blocks
                if let Some(hir_id) = region_scope.hir_id(self.scope_tree)
                    && is_ghost_block(self.tcx, hir_id)
                {
                    AnfValue::Unit
                } else if let Loop { body } = &self.thir[*value].kind {
                    let mut body = self.a_normal_form_expr_block(*body)?;
                    body.label = Some(*region_scope);
                    bind_var(stmts, AnfOp::loop_(body))
                } else {
                    self.a_normal_form_expr(*value, stmts)?.0
                }
            }
            Loop { body } => {
                let body = self.a_normal_form_expr_block(*body)?;
                bind_var(stmts, AnfOp::loop_(body))
            }
            Break { label, value } => {
                let label = (AnfValue::Label(*label), label.span(self.tcx, self.scope_tree));
                let value = value.map(|value| self.a_normal_form_expr(value, stmts)).transpose()?;
                bind_var(stmts, AnfOp::break_(label, value))
            }
            Block { block } => self.a_normal_form_block(*block, stmts)?,
            VarRef { id } => match self.alias.get(&id.0.local_id) {
                Some(VarValue::Mutable) => {
                    let borrow = AnfValue::Borrow(AnfPlace::mut_var(self.var(*id)).into());
                    bind_var(stmts, AnfOp::read((borrow, expr.span)))
                }
                Some(VarValue::Value(v)) => v.clone(),
                None => AnfValue::Unit,
            },
            Call { fun, args, .. } => {
                let fun = self.a_normal_form_expr(*fun, stmts)?;
                match fun.0 {
                    AnfValue::Fn(fun_id, _)
                        if let Some(ctx) = self.ctx
                            && Intrinsic::SnapshotFromFn.is(ctx, fun_id) =>
                    {
                        AnfValue::Unit
                    }
                    AnfValue::Fn(fun_id, subst) => 'fun: {
                        let args = args
                            .iter()
                            .map(|arg| self.a_normal_form_expr(*arg, stmts))
                            .collect::<Result<::std::boxed::Box<[_]>, _>>()?;
                        let (fun_id_resolved, subst_resolved) =
                            TraitResolved::resolve_item(self.tcx, self.typing_env, fun_id, subst.0)
                                .to_opt(fun_id, subst.0)
                                .unwrap_or_else(|| {
                                    self.tcx.crash_and_error(
                                        self.span(),
                                        "could not resolve call in `#[erasure]` check",
                                    )
                                });
                        let (fun_id, subst, args) = if let Some(erased) =
                            self.ctx.and_then(|ctx| ctx.erasure(fun_id_resolved))
                        {
                            let Some(erased) = erased else { break 'fun AnfValue::Unit };
                            let args = args
                                .into_iter()
                                .zip(&erased.erase_args)
                                .filter_map(|(arg, &erase)| if erase { None } else { Some(arg) })
                                .collect();
                            let subst = ty::EarlyBinder::bind(erased.def.1)
                                .instantiate(self.tcx, subst_resolved);
                            (erased.def.0, (*subst).into(), args)
                        } else if let Some(ctx) = self.ctx
                            && let Intrinsic::PtrOwnAsRef | Intrinsic::PtrOwnAsMut =
                                ctx.intrinsic(fun_id)
                        {
                            let arg0 = args.into_iter().next().unwrap();
                            let mut place = std::boxed::Box::new(AnfPlace::immut(arg0.0));
                            place.add_deref(true); // Add unsafe deref
                            break 'fun bind_var(
                                stmts,
                                AnfOp::unsafe_borrow((AnfValue::Borrow(place), arg0.1)),
                            );
                        } else if let Some(ctx) = self.ctx
                            && let Intrinsic::PtrOwnFromRef | Intrinsic::PtrOwnFromMut =
                                ctx.intrinsic(fun_id)
                        {
                            let arg0 = args.into_iter().next().unwrap();
                            let mut place = AnfPlace::immut(arg0.0);
                            place.add_deref(false);
                            break 'fun place.raw_borrow();
                        } else {
                            (fun_id, subst, args)
                        };
                        bind_var(stmts, AnfOp::call(fun_id, subst, args))
                    }
                    _ => {
                        return Err(
                            self.unsupported_syntax(fun.1, "unsupported function expression")
                        );
                    }
                }
            }
            ZstLiteral { .. } => match expr.ty.kind() {
                ty::TyKind::FnDef(def_id, subst) => AnfValue::Fn(*def_id, (*subst).into()),
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
            ConstParam { param, .. } => AnfValue::Const(ty::Const::new_param(self.tcx, *param)),
            Deref { arg } => {
                let arg = self.a_normal_form_expr(*arg, stmts)?;
                bind_var(stmts, AnfOp::deref(arg))
            }
            // Reborrows
            Borrow { arg, .. } if let Deref { arg } = self.unscope(*arg) => {
                let arg_ty = &self.thir[*arg].ty;
                let (val, span) = self.a_normal_form_expr(*arg, stmts)?;
                if arg_ty.is_ref() {
                    val // safe reborrows are ignored
                } else {
                    assert!(arg_ty.is_raw_ptr());
                    let mut place = AnfPlace::immut(val);
                    place.add_deref(true);
                    let bor = AnfValue::Borrow(place.into());
                    bind_var(stmts, AnfOp::unsafe_borrow((bor, span)))
                }
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
            RawBorrow { arg, mutability: _ } => {
                let place = self.a_normal_form_place(*arg, stmts)?;
                if place.is_unsafe() {
                    let bor = AnfValue::Borrow(std::boxed::Box::new(place));
                    bind_var(stmts, AnfOp::unsafe_borrow((bor, self.thir[*arg].span)))
                } else {
                    place.raw_borrow()
                }
            }
            Tuple { fields } => {
                // Visit all fields even if they have type `Ghost<_>` because they may all have effects
                // It's just their values we may discard in the end.
                let values = fields
                    .iter()
                    .map(|f| self.a_normal_form_expr(*f, stmts))
                    .collect::<Result<::std::boxed::Box<[_]>, _>>()?;
                if fields.len() >= 1
                    && fields.iter().skip(1).all(|e| is_ghost_or_snap(self.tcx, self.thir[*e].ty))
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
            Use { source } => self.a_normal_form_expr(*source, stmts)?.0,
            Cast { source } => {
                use rustc_type_ir::TyKind::{RawPtr, Slice};
                let value = self.a_normal_form_expr(*source, stmts)?.0;
                let source_ty = self.thir[*source].ty;
                // {source_ty} == *const [T] and {expr.ty} == *const T
                let is_ptr_slice_ty = match (source_ty.kind(), expr.ty.kind()) {
                    (RawPtr(pointee, _), RawPtr(elem_ty2, _)) => match pointee.kind() {
                        Slice(elem_ty) => elem_ty == elem_ty2,
                        _ => false,
                    },
                    _ => false,
                };
                if is_ptr_slice_ty {
                    AnfValue::Thin(value.into())
                } else if is_noop_cast(self.tcx, self.typing_env, source_ty, expr.ty) {
                    value
                } else {
                    AnfValue::Cast(source_ty, expr.ty, value.into())
                }
            }
            Field { lhs, variant_index, name } => {
                let value = self.a_normal_form_expr(*lhs, stmts)?.0;
                AnfValue::Field(*variant_index, *name, value.into())
            }
            ValueTypeAscription { source, .. } => self.a_normal_form_expr(*source, stmts)?.0,
            kind => {
                return Err(self.unsupported_syntax_with_note(
                    expr.span,
                    "unsupported expression",
                    format!("unsupported: {kind:?}"),
                ));
            }
        };
        Ok((value, expr.span))
    }

    fn unscope(&self, mut expr_id: ExprId) -> &ExprKind<'tcx> {
        loop {
            match &self.thir[expr_id].kind {
                ExprKind::Scope { value, .. } => expr_id = *value,
                k => return k,
            }
        }
    }

    fn a_normal_form_place(
        &mut self,
        expr_id: ExprId,
        stmts: &mut Vec<AnfStmt<'tcx>>,
    ) -> Result<AnfPlace<'tcx>, ()> {
        let expr = &self.thir[expr_id];
        use ExprKind::*;
        match &expr.kind {
            VarRef { id } => match self.alias.get(&id.0.local_id) {
                Some(VarValue::Mutable) => Ok(AnfPlace::mut_var(self.var(*id))),
                Some(VarValue::Value(v)) => Ok(AnfPlace::immut(v.clone())),
                None => Ok(AnfPlace::immut(AnfValue::Unit)), // Ghost place
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
            Field { lhs, variant_index, name } => {
                let place = self.a_normal_form_place(*lhs, stmts)?;
                Ok(place.field(*variant_index, *name))
            }
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
    ) -> Result<AnfValue<'tcx>, ()> {
        let block = &self.thir[block];
        if block.targeted_by_break {
            self.tcx.warn(block.span, "#[refines] does not yet support `break` on labeled blocks");
        }
        for stmt in &block.stmts {
            self.a_normal_form_stmt(*stmt, stmts)?;
        }
        match block.expr {
            None => Ok(AnfValue::Unit),
            Some(e) => Ok(self.a_normal_form_expr(e, stmts)?.0),
        }
    }

    fn a_normal_form_expr_block(&mut self, expr_id: ExprId) -> Result<AnfBlock<'tcx>, ()> {
        self.a_normal_form_expr_block_(expr_id, AnfPattern::Wild, Vec::new(), None)
    }

    fn a_normal_form_expr_block_(
        &mut self,
        expr_id: ExprId,
        pattern: AnfPattern,
        mut stmts: Vec<AnfStmt<'tcx>>,
        span: Option<Span>,
    ) -> Result<AnfBlock<'tcx>, ()> {
        let ret = self.a_normal_form_expr(expr_id, &mut stmts)?;
        let span = span.unwrap_or(ret.1);
        Ok(AnfBlock { label: None, pattern, stmts, ret, span })
    }

    fn a_normal_form_arm(&mut self, arm_id: ArmId) -> Result<AnfBlock<'tcx>, ()> {
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
    ) -> Result<(), ()> {
        let stmt = &self.thir[stmt];
        use thir::StmtKind::*;
        match &stmt.kind {
            Expr { expr, .. } => {
                let _ = self.a_normal_form_expr(*expr, stmts)?;
            }
            Let { pattern, initializer, else_block, span, .. } => {
                let Some(initializer) = initializer else {
                    return Err(
                        self.unsupported_syntax(*span, "unsupported let without initializer")
                    );
                };
                if is_erasable(self.tcx, self.thir, *initializer) {
                    if let Some(_) = else_block {
                        return Err(self.unsupported_syntax(
                            *span,
                            "unexpected let-else in erased let (this shouldn't happen)",
                        ));
                    }
                    return Ok(());
                }
                let rhs = self.a_normal_form_expr(*initializer, stmts)?;
                let mut pattern = &**pattern;
                loop {
                    match &pattern.kind {
                        PatKind::Binding { .. } if is_ghost_or_snap(self.tcx, pattern.ty) => {
                            return Ok(());
                        }
                        PatKind::Binding {
                            var,
                            mode: BindingMode(ByRef::No, Mutability::Not),
                            subpattern: None,
                            ..
                        } => {
                            // Skip generating a binding
                            self.alias.insert(var.0.local_id, VarValue::Value(rhs.0.clone()));
                            return Ok(());
                        }
                        PatKind::Leaf { subpatterns }
                            if subpatterns.len() >= 1
                                && subpatterns
                                    .iter()
                                    .skip(1)
                                    .all(|p| is_ghost_or_snap(self.tcx, p.pattern.ty)) =>
                        {
                            // Erase ghost fields
                            pattern = &subpatterns[0].pattern;
                        }
                        // Nothing to bind, skip statement. Effects of the initializer are already in `stmts`
                        PatKind::Wild => return Ok(()),
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
                            AnfBlock {
                                label: None,
                                pattern: AnfPattern::Wild,
                                stmts,
                                ret: (val, span),
                                span,
                            },
                        )
                    }
                };
                let lhs = self.a_normal_form_pat(&pattern)?;
                stmts.push(AnfStmt { pattern: lhs, rhs, span: *span });
            }
        }
        Ok(())
    }

    fn a_normal_form_pat(&mut self, pat: &thir::Pat<'tcx>) -> Result<AnfPattern, ()> {
        use PatKind::*;
        match &pat.kind {
            Wild => Ok(AnfPattern::Wild),
            Binding { var, mode: BindingMode(ByRef::No, mutability), .. } => {
                let v = self.var(*var);
                self.alias.insert(
                    var.0.local_id,
                    match mutability {
                        Mutability::Not => VarValue::Value(AnfValue::Var(v)),
                        Mutability::Mut => VarValue::Mutable,
                    },
                );
                Ok(AnfPattern::Var(v))
            }
            Binding { var, .. } => Ok(AnfPattern::Var(self.var(*var))),
            Leaf { subpatterns } => {
                let subpatterns = subpatterns
                    .iter()
                    .map(|p| self.a_normal_form_pat(&p.pattern))
                    .collect::<Result<::std::boxed::Box<[_]>, _>>()?;
                // the actual constructor doesn't matter for a `Leaf` so we just use `Tuple`
                Ok(AnfPattern::Ctor(Ctor::Tuple, subpatterns, pat.span))
            }
            Variant { adt_def, args: _, variant_index, subpatterns } => {
                let subpatterns = subpatterns
                    .iter()
                    .map(|p| self.a_normal_form_pat(&p.pattern))
                    .collect::<Result<Box<[_]>, _>>()?;
                Ok(AnfPattern::Ctor(
                    Ctor::Adt(adt_def.did(), *variant_index),
                    subpatterns,
                    pat.span,
                ))
            }
            Deref { subpattern } => {
                let subpattern = self.a_normal_form_pat(&**subpattern)?;
                Ok(AnfPattern::Deref(subpattern.into()))
            }
            Constant { value } if value.ty.is_bool() => {
                let b = value.try_to_bool().unwrap();
                Ok(AnfPattern::Ctor(Ctor::Bool(b), [].into(), pat.span))
            }
            kind => Err(self.unsupported_syntax_with_note(
                pat.span,
                "unsupported pattern",
                format!("unsupported: {kind:?}"),
            )),
        }
    }

    fn var(&self, hir_id: thir::LocalVarId) -> Var {
        assert!(hir_id.0.owner.def_id == self.def_id);
        Var::HirId(hir_id.0.local_id)
    }
}

fn is_noop_cast<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    from: ty::Ty<'tcx>,
    to: ty::Ty<'tcx>,
) -> bool {
    use rustc_type_ir::TyKind::RawPtr;
    match (from.kind(), to.kind()) {
        (RawPtr(from_ty, _), RawPtr(to_ty, _)) => {
            (from_ty.is_sized(tcx, typing_env) && to_ty.is_sized(tcx, typing_env))
                || from_ty.is_slice() && to_ty.is_slice()
        }
        _ => false,
    }
}

fn is_erasable(tcx: TyCtxt, thir: &Thir, expr: ExprId) -> bool {
    let mut expr = &thir[expr];
    loop {
        match expr.kind {
            ExprKind::Scope { value, .. } => expr = &thir[value],
            ExprKind::Closure(box thir::ClosureExpr { closure_id, .. }) => {
                let closure_id = closure_id.to_def_id();
                return is_spec(tcx, closure_id)
                    || is_erasure(tcx, closure_id)
                    || is_before_loop(tcx, closure_id);
            }
            _ => return false,
        }
    }
}

////////////////////////////////////////////////////////////////
// * Equality checking
////////////////////////////////////////////////////////////////

struct EqualityChecker<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// ID of the function with the `#[erasure]` attribute
    def_id: LocalDefId,
    /// Warning or Error
    level: rustc_errors::Level,
    equate_var: HashMap<Var, Var>,
    equate_label: HashMap<Scope, Scope>,
}

impl<'tcx> EqualityChecker<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId, level: rustc_errors::Level) -> Self {
        let equate_var = HashMap::new();
        let equate_label = HashMap::new();
        EqualityChecker { tcx, def_id, level, equate_var, equate_label }
    }

    fn equate_value(&self, v1: &AnfValue<'tcx>, v2: &AnfValue<'tcx>) -> bool {
        use AnfValue::*;
        match (v1, v2) {
            (Unit, Unit) => true,
            (Var(v1), Var(v2)) => {
                let Some(v1_) = self.equate_var.get(v1) else { return false };
                v1_ == v2
            }
            (Literal(lit1, neg1), Literal(lit2, neg2)) => lit1 == lit2 && neg1 == neg2,
            (Const(p1), Const(p2)) => p1 == p2,
            (Borrow(place1), Borrow(place2)) => self.equate_place(place1, place2),
            (RawBorrow(place1), RawBorrow(place2)) => self.equate_place(place1, place2),
            (Ctor(c1, args1), Ctor(c2, args2)) => {
                c1 == c2
                    && args1.len() == args2.len()
                    && args1.iter().zip(args2).all(|(a1, a2)| self.equate_value(&a1.0, &a2.0))
            }
            (Field(variant1, field1, v1), Field(variant2, field2, v2)) => {
                variant1 == variant2 && field1 == field2 && self.equate_value(v1, v2)
            }
            (Fn(f1, s1), Fn(f2, s2)) => f1 == f2 && s1 == s2,
            (Cast(from1, to1, value1), Cast(from2, to2, value2)) => {
                from1 == from2 && to1 == to2 && self.equate_value(value1, value2)
            }
            (Thin(v1), Thin(v2)) => self.equate_value(v1, v2),
            (Label(l1), Label(l2)) => {
                let Some(l1_) = self.equate_label.get(l1) else { return false };
                l1_ == l2
            }
            _ => false,
        }
    }

    fn equate_place(&self, p1: &AnfPlace<'tcx>, p2: &AnfPlace<'tcx>) -> bool {
        let equate_base = match (&p1.base, &p2.base) {
            (AnfPlaceBase::MutVar(v1), AnfPlaceBase::MutVar(v2)) => {
                let Some(v1_) = self.equate_var.get(v1) else { return false };
                v1_ == v2
            }
            (AnfPlaceBase::ImmutVar(v1), AnfPlaceBase::ImmutVar(v2)) => self.equate_value(v1, v2),
            _ => false,
        };
        equate_base && p1.projections == p2.projections
    }

    fn equate_pat(&mut self, pat1: &AnfPattern, pat2: &AnfPattern) -> Result<(), ()> {
        match (pat1, pat2) {
            (AnfPattern::Var(v1), AnfPattern::Var(v2)) => {
                self.new_var(*v1, *v2);
            }
            (AnfPattern::Ctor(c1, args1, span1), AnfPattern::Ctor(c2, args2, span2)) => {
                if c1 == c2 {
                    for (a1, a2) in args1.into_iter().zip(args2.into_iter()) {
                        self.equate_pat(a1, a2)?;
                    }
                } else {
                    return Err(self.error(*span1, "#[erasure] pattern", *span2, "target pattern"));
                }
            }
            (AnfPattern::Deref(pat1), AnfPattern::Deref(pat2)) => {
                self.equate_pat(pat1, pat2)?;
            }
            (AnfPattern::Wild, _) | (_, AnfPattern::Wild) => {}
            _ => {}
        }
        Ok(())
    }

    fn new_var(&mut self, v1: Var, v2: Var) {
        self.equate_var.insert(v1, v2);
    }

    fn new_label(&mut self, l1: Option<Scope>, l2: Option<Scope>) {
        let (Some(l1), Some(l2)) = (l1, l2) else { return };
        self.equate_label.insert(l1, l2);
    }

    fn equate_stmts(
        &mut self,
        left: &[AnfStmt<'tcx>],
        right: &[AnfStmt<'tcx>],
        left_span: Span,
        right_span: Span,
    ) -> Result<(), ()> {
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
                        format!(
                            " ({}{})",
                            self.tcx.def_path_str(def_id),
                            if subst.0.len() == 0 {
                                String::new()
                            } else {
                                subst.0.print_as_list()
                            }
                        )
                    }
                    _ => format!(" ({:?})", tag),
                }
            };
            if left.rhs.tag != right.rhs.tag || left.rhs.args.len() != right.rhs.args.len() {
                return Err(self.error(
                    left.span,
                    format!("#[erasure] expression{}", debug_string(left.rhs.tag)),
                    right.span,
                    format!("target expression{}", debug_string(right.rhs.tag)),
                ));
            }
            for (left, right) in left.rhs.args.iter().zip(&right.rhs.args) {
                if !self.equate_value(&left.0, &right.0) {
                    return Err(self.error(
                        left.1,
                        format!("#[erasure] expression ({:?})", left.0),
                        right.1,
                        format!("erased expression ({:?})", right.0),
                    ));
                }
            }
            for (left, right) in left.rhs.arms.iter().zip(&right.rhs.arms) {
                self.equate(left, right)?;
            }
            match left.rhs.arms.len().cmp(&right.rhs.arms.len()) {
                Equal => {}
                Less => {
                    let right_span = right.rhs.arms[left.rhs.arms.len()].span;
                    return Err(self.error(
                        right_span,
                        "target block (mismatched block)",
                        left.span,
                        "#[erasure] expression (no matching block)",
                    ));
                }
                Greater => {
                    let left_span = left.rhs.arms[right.rhs.arms.len()].span;
                    return Err(self.error(
                        left_span,
                        "#[erasure] block (mismatched block)",
                        right.span,
                        "target expression (no matching block)",
                    ));
                }
            }
            self.equate_pat(&left.pattern, &right.pattern)?;
        }
        match left.len().cmp(&right.len()) {
            Equal => {}
            Less => {
                let right_span = right[left.len()].span;
                return Err(self.error(
                    right_span,
                    "target block (mismatched statement)",
                    left_span,
                    "#[erasure] block (no matching statement)",
                ));
            }
            Greater => {
                let left_span = left[right.len()].span;
                return Err(self.error(
                    left_span,
                    "#[erasure] block (mismatched statement)",
                    right_span,
                    "target block (no matching statement)",
                ));
            }
        }
        Ok(())
    }

    fn equate(&mut self, left: &AnfBlock<'tcx>, right: &AnfBlock<'tcx>) -> Result<(), ()> {
        self.new_label(left.label, right.label);
        self.equate_pat(&left.pattern, &right.pattern)?;
        self.equate_stmts(&left.stmts, &right.stmts, left.span, right.span)?;
        if self.equate_value(&left.ret.0, &right.ret.0) {
            Ok(())
        } else {
            Err(self.error(
                left.ret.1,
                "#[erasure] side (mismatched value)",
                right.ret.1,
                "target side",
            ))
        }
    }

    fn error(
        &self,
        span: Span,
        msg: impl Into<SubdiagMessage>,
        span2: Span,
        msg2: impl Into<SubdiagMessage>,
    ) {
        warn_or_error(
            self.tcx,
            self.level,
            span,
            format!("failed #[erasure] check for {}", self.tcx.def_path_str(self.def_id)),
        )
        .with_span_label(span, msg)
        .with_span_label(span2, msg2)
        .emit();
    }
}

// * Pretty-printing

struct Pretty<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: Option<LocalDefId>,
    body: &'a AnfBlock<'tcx>,
}

impl<'a, 'tcx> std::fmt::Debug for Pretty<'a, 'tcx> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        let printer = PrintAnf::new(self.tcx, self.owner);
        printer.print_body(&self.body, f)
    }
}

/// Pretty printer of ANF terms.
struct PrintAnf<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: Option<LocalDefId>,
    indent: usize,
}

impl<'tcx> PrintAnf<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, owner: Option<LocalDefId>) -> Self {
        PrintAnf { tcx, owner, indent: 0 }
    }

    fn indent(&self) -> Self {
        PrintAnf { indent: self.indent + 1, ..*self }
    }

    fn print_indent(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        for _ in 0..self.indent {
            write!(f, "  ")?;
        }
        Ok(())
    }

    fn print_body(&self, body: &AnfBlock<'tcx>, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        self.print_indent(f)?;
        if let Some(label) = body.label {
            write!(f, "'")?;
            self.print_hir_id(label.local_id, f)?;
            write!(f, ": ")?;
        }
        self.print_pattern(&body.pattern, f)?;
        writeln!(f, " => {{")?;
        let indented = self.indent();
        for stmt in &body.stmts {
            indented.print_stmt(stmt, f)?
        }
        indented.print_indent(f)?;
        indented.print_value(&body.ret.0, f)?;
        writeln!(f, "")?;
        self.print_indent(f)?;
        writeln!(f, "}}")?;
        Ok(())
    }

    fn print_pattern(&self, pat: &AnfPattern, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        use AnfPattern::*;
        match pat {
            Wild => write!(f, "_"),
            Var(var) => self.print_var(*var, f),
            Ctor(self::Ctor::Tuple, anf_patterns, _) => {
                write!(f, "(")?;
                for (i, p) in anf_patterns.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    self.print_pattern(p, f)?;
                }
                write!(f, ")")
            }
            Ctor(ctor, anf_patterns, _) => {
                self.print_ctor(ctor, f)?;
                if anf_patterns.len() != 0 {
                    write!(f, "(")?;
                    for (i, p) in anf_patterns.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        self.print_pattern(p, f)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Deref(anf_pattern) => {
                write!(f, "*")?;
                self.print_pattern(anf_pattern, f)
            }
        }
    }

    fn print_ctor(&self, ctor: &Ctor, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match ctor {
            Ctor::Tuple => write!(f, "Tuple"),
            Ctor::Array => write!(f, "Array"),
            Ctor::Adt(def_id, variant_index) => {
                let adt_def = self.tcx.adt_def(*def_id);
                let variant = &adt_def.variants()[*variant_index];
                write!(f, "{}", self.tcx.def_path_str(variant.def_id))
            }
            Ctor::Bool(b) => write!(f, "{}", b),
        }
    }

    fn print_var(&self, var: Var, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match var {
            Var::HirId(hir_id) => self.print_hir_id(hir_id, f),
            Var::ExprId(expr_id) => write!(f, "#e{}", expr_id.as_u32()),
        }
    }

    fn print_stmt(&self, stmt: &AnfStmt<'tcx>, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        self.print_indent(f)?;
        self.print_pattern(&stmt.pattern, f)?;
        write!(f, " = ")?;
        self.print_op(&stmt.rhs, f)
    }

    fn print_op(&self, op: &AnfOp<'tcx>, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        self.print_op_tag(&op.tag, f)?;
        if op.args.len() != 0 {
            write!(f, "(")?;
            for (i, arg) in op.args.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                self.print_value(&arg.0, f)?;
            }
            write!(f, ")")?;
        }
        writeln!(f, "")?;
        if op.arms.len() != 0 {
            for arm in &op.arms {
                self.print_body(arm, f)?;
            }
        }
        Ok(())
    }

    fn print_op_tag(&self, tag: &OpTag<'tcx>, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        use OpTag::*;
        match tag {
            Value => write!(f, "value"),
            Read => write!(f, "read"),
            Call(def_id, subst) => {
                write!(
                    f,
                    "call {}{}",
                    self.tcx.def_path_str(def_id),
                    if subst.0.len() == 0 { String::new() } else { subst.0.print_as_list() }
                )
            }
            BinOp(op) => write!(f, "{:?}", op),
            UnOp(op) => write!(f, "{:?}", op),
            LogicalOp(op) => write!(f, "{:?}", op),
            If => write!(f, "if"),
            IfLet => write!(f, "iflet"),
            Match => write!(f, "match"),
            LetElse => write!(f, "letelse"),
            Return => write!(f, "return"),
            Deref => write!(f, "deref"),
            UnsafeBorrow => write!(f, "unsafe_borrow"),
            Const(def_id, _) => write!(f, "const {}", self.tcx.def_path_str(def_id)),
            Guard => write!(f, "guard"),
            Break => write!(f, "break"),
            Loop => write!(f, "loop"),
        }
    }

    fn print_place(
        &self,
        place: &AnfPlace<'tcx>,
        f: &mut Formatter,
    ) -> Result<(), std::fmt::Error> {
        match &place.base {
            AnfPlaceBase::MutVar(v) => self.print_var(*v, f)?,
            AnfPlaceBase::ImmutVar(v) => self.print_value(v, f)?,
        }
        for proj in &place.projections {
            use AnfProjection::*;
            match proj {
                Deref { unsafe_: _ } => {
                    write!(f, ".deref")?;
                }
                Field { variant: _, field } => {
                    write!(f, ".{field:?}")?;
                }
            }
        }
        Ok(())
    }

    fn print_value(
        &self,
        value: &AnfValue<'tcx>,
        f: &mut Formatter,
    ) -> Result<(), std::fmt::Error> {
        use AnfValue::*;
        match value {
            Unit => write!(f, "()"),
            Var(v) => self.print_var(*v, f),
            Literal(lit, neg) => {
                if *neg {
                    write!(f, "-")?;
                }
                write!(f, "{:?}", lit)
            }
            Const(c) => write!(f, "{:?}", c),
            Borrow(place) => {
                write!(f, "&")?;
                self.print_place(place, f)
            }
            RawBorrow(place) => {
                write!(f, "&raw ")?;
                self.print_place(place, f)
            }
            Ctor(ctor, args) => {
                self.print_ctor(ctor, f)?;
                if args.len() != 0 {
                    write!(f, "(")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        self.print_value(&arg.0, f)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Field(variant, field, value) => {
                write!(f, "Field({variant:?}, {field:?},")?;
                self.print_value(value, f)?;
                write!(f, ")")
            }
            Fn(def_id, subst) => write!(
                f,
                "fn {}{}",
                self.tcx.def_path_str(def_id),
                if subst.0.len() == 0 { String::new() } else { subst.0.print_as_list() }
            ),
            Cast(from, to, value) => {
                write!(f, "Cast({:?}, {:?}, ", from, to)?;
                self.print_value(value, f)?;
                write!(f, ")")
            }
            Thin(v) => {
                write!(f, "Thin(")?;
                self.print_value(v, f)?;
                write!(f, ")")
            }
            Label(label) => {
                write!(f, "'")?;
                self.print_hir_id(label.local_id, f)
            }
        }
    }

    fn print_hir_id(
        &self,
        local_id: ItemLocalId,
        f: &mut Formatter,
    ) -> Result<(), std::fmt::Error> {
        match self.owner {
            Some(def_id) => {
                let hir_id = rustc_hir::HirId { owner: rustc_hir::OwnerId { def_id }, local_id };
                write!(f, "{}", self.tcx.hir_name(hir_id))
            }
            None => write!(f, "#h{}", local_id.as_u32()),
        }
    }
}
