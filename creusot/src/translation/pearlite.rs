// A poorly named module.
//
// Entrypoint for translation of all Pearlite specifications and code: #[logic], contracts, proof_assert!
//
// Transforms THIR into a Term which may be serialized in Creusot metadata files for usage by dependent crates
// The `lower` module then transforms a `Term` into a WhyML expression.

use crate::{
    contracts_items::{Intrinsic, is_assertion, is_logic_closure, is_spec},
    error::{CreusotResult, Error},
    translation::TranslationCtx,
};
use log::*;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::{ByRef, LitIntType, LitKind, Mutability, visit::VisitorResult};
use rustc_hir::{
    HirId, OwnerId,
    def_id::{DefId, LocalDefId},
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
pub(crate) use rustc_middle::thir;
use rustc_middle::{
    mir::{BorrowKind, Mutability::*, ProjectionElem},
    thir::{
        AdtExpr, ArmId, Block, ClosureExpr, ExprId, ExprKind, Pat, PatKind, StmtId, StmtKind, Thir,
    },
    ty::{
        Const, GenericArgsRef, ParamConst, Ty, TyCtxt, TyKind, TypeFoldable, TypeVisitable,
        TypingEnv, adjustment::PointerCoercion,
    },
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{DUMMY_SP, Span, sym};
use rustc_type_ir::{FloatTy, IntTy, Interner, UintTy};
use std::{
    assert_matches::assert_matches,
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
};

mod normalize;

pub(crate) use normalize::*;

#[derive(Copy, Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Lt,
    Le,
    Ge,
    Gt,
    Eq,
    Ne,
    And,
    Or,
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub struct Term<'tcx> {
    pub ty: Ty<'tcx>,
    pub kind: TermKind<'tcx>,
    pub span: Span,
}

#[derive(
    Copy, Clone, Debug, Eq, PartialEq, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable,
)]
pub enum QuantKind {
    Forall,
    Exists,
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub struct Trigger<'tcx>(pub(crate) Box<[Term<'tcx>]>);

pub type QuantBinder<'tcx> = Box<[(PIdent, Ty<'tcx>)]>;

pub type Projections<V, T> = Box<[ProjectionElem<V, T>]>;

/// Reuse why3 identifiers for fmir and pearlite ASTs.
pub type Ident = why3::Ident;

/// Pearlite Ident
/// This wrapper implements traits from rustc's API:
/// `TypeVisitable`, `TypeFoldable`, `Decodable`, `Encodable` (associated with the derive macros `TyDecodable` and `TyEncodable`).
/// Use `PIdent` inside types that will also implement those traits.
/// Otherwise, try to use `Ident` as much as possible for uniformity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PIdent(pub Ident);

impl From<Ident> for PIdent {
    fn from(ident: Ident) -> Self {
        PIdent(ident)
    }
}

impl<I: Interner> TypeVisitable<I> for PIdent {
    fn visit_with<V>(&self, _: &mut V) -> <V as rustc_middle::ty::TypeVisitor<I>>::Result
    where
        V: rustc_middle::ty::TypeVisitor<I>,
    {
        V::Result::output()
    }
}

impl<I: Interner> TypeFoldable<I> for PIdent {
    fn try_fold_with<F>(
        self,
        _: &mut F,
    ) -> Result<Self, <F as rustc_middle::ty::FallibleTypeFolder<I>>::Error>
    where
        F: rustc_middle::ty::FallibleTypeFolder<I>,
    {
        Ok(self)
    }

    fn fold_with<F: rustc_type_ir::TypeFolder<I>>(self, _: &mut F) -> Self {
        self
    }
}

impl<T: Decoder> Decodable<T> for PIdent {
    fn decode(decoder: &mut T) -> Self {
        let id = decoder.read_u64();
        let path = why3::Symbol::intern(decoder.read_str());
        let name = decoder.read_str();
        PIdent(Ident::unsafe_build(name, path, id))
    }
}

impl<T: Encoder> Encodable<T> for PIdent {
    fn encode(&self, encoder: &mut T) {
        encoder.emit_u64(self.0.id());
        encoder.emit_str(&self.0.src().to_string());
        encoder.emit_str(&self.0.name().to_string());
    }
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum TermKind<'tcx> {
    Var(PIdent),
    Lit(Literal<'tcx>),
    /// Will compile to `Seq.create $n [| $e0; ...; $e(n-1) |]`
    SeqLiteral(Box<[Term<'tcx>]>),
    Cast {
        arg: Box<Term<'tcx>>,
    },
    Coerce {
        arg: Box<Term<'tcx>>,
    },
    Item(DefId, GenericArgsRef<'tcx>),
    /// Constants. May get substituted using `instantiate` (via `TypeFoldable`).
    Const(Const<'tcx>),
    Assert {
        cond: Box<Term<'tcx>>,
    },
    Binary {
        op: BinOp,
        lhs: Box<Term<'tcx>>,
        rhs: Box<Term<'tcx>>,
    },
    Unary {
        op: UnOp,
        arg: Box<Term<'tcx>>,
    },
    Quant {
        kind: QuantKind,
        binder: QuantBinder<'tcx>,
        trigger: Box<[Trigger<'tcx>]>,
        body: Box<Term<'tcx>>,
    },
    // TODO: Get rid of (id, subst).
    Call {
        id: DefId,
        subst: GenericArgsRef<'tcx>,
        args: Box<[Term<'tcx>]>,
    },
    Constructor {
        variant: VariantIdx,
        fields: Box<[Term<'tcx>]>,
    },
    Tuple {
        fields: Box<[Term<'tcx>]>,
    },
    Cur {
        term: Box<Term<'tcx>>,
    },
    Fin {
        term: Box<Term<'tcx>>,
    },
    Impl {
        lhs: Box<Term<'tcx>>,
        rhs: Box<Term<'tcx>>,
    },
    /// Pearlite matches must be non-empty.
    Match {
        scrutinee: Box<Term<'tcx>>,
        arms: Box<[(Pattern<'tcx>, Term<'tcx>)]>,
    },
    Let {
        pattern: Pattern<'tcx>,
        arg: Box<Term<'tcx>>,
        body: Box<Term<'tcx>>,
    },
    /// A field projection from a *struct* or *closure*.
    ///
    /// Unlike MIR projections this does *not* include projections from enums.
    /// It corresponds strictly to the syntactic projection f.x
    Projection {
        lhs: Box<Term<'tcx>>,
        idx: FieldIdx,
    },
    Old {
        term: Box<Term<'tcx>>,
    },
    Closure {
        bound: Box<[(PIdent, Ty<'tcx>)]>,
        body: Box<Term<'tcx>>,
    },
    Reborrow {
        inner: Box<Term<'tcx>>,
        projections: Projections<Term<'tcx>, Ty<'tcx>>,
    },
    /// Inferred preconditions for `(item, args)`
    Precondition {
        item: DefId,
        subst: GenericArgsRef<'tcx>,
        params: Box<[Term<'tcx>]>,
    },
    /// Inferred postconditions for `(item, args)`
    Postcondition {
        item: DefId,
        subst: GenericArgsRef<'tcx>,
        params: Box<[Term<'tcx>]>,
    },
}

impl<I: Interner> TypeFoldable<I> for Literal<'_> {
    fn try_fold_with<F: rustc_middle::ty::FallibleTypeFolder<I>>(
        self,
        _: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(self)
    }

    fn fold_with<F: rustc_type_ir::TypeFolder<I>>(self, _: &mut F) -> Self {
        self
    }
}

impl<I: Interner> TypeVisitable<I> for Literal<'_> {
    fn visit_with<V: rustc_middle::ty::TypeVisitor<I>>(&self, _: &mut V) -> V::Result {
        V::Result::output()
    }
}

pub fn visit_projections<V, T>(v: &Projections<V, T>, mut f: impl FnMut(&V)) {
    v.iter().for_each(|elem| {
        if let ProjectionElem::Index(v) = elem {
            f(v)
        }
    })
}

pub fn visit_projections_mut<V, T>(v: &mut Projections<V, T>, mut f: impl FnMut(&mut V)) {
    v.iter_mut().for_each(|elem| {
        if let ProjectionElem::Index(v) = elem {
            f(v)
        }
    })
}

#[derive(Clone, Debug)]
pub struct Float(pub f64);

impl<E: Encoder> Encodable<E> for Float {
    fn encode(&self, s: &mut E) {
        s.emit_u64(self.0.to_bits())
    }
}

impl<E: Decoder> Decodable<E> for Float {
    fn decode(s: &mut E) -> Float {
        Float(f64::from_bits(s.read_u64()))
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
        Float(value)
    }
}

// FIXME: Clean up this type: clarify use of ZST, Function, Integer types
#[derive(Clone, Debug, TyDecodable, TyEncodable)]
pub enum Literal<'tcx> {
    Char(char),
    Bool(bool),
    // TODO: Find a way to make this a BigInt type
    Integer(i128),
    UInteger(u128),
    MachSigned(i128, IntTy),
    MachUnsigned(u128, UintTy),
    Float(Float, FloatTy),
    String(String),
    ZST,
    Function(DefId, GenericArgsRef<'tcx>),
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub struct Pattern<'tcx> {
    pub ty: Ty<'tcx>,
    pub kind: PatternKind<'tcx>,
    pub span: Span,
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum PatternKind<'tcx> {
    // Subpatterns are always sorted by field index
    Constructor(VariantIdx, Box<[(FieldIdx, Pattern<'tcx>)]>),
    /// Matches the pointed element of a pointer, so for `Box<T>` it matches `T`,
    /// for mutable borrows it matches the *current* value
    Deref(Box<Pattern<'tcx>>),
    Tuple(Box<[Pattern<'tcx>]>),
    Wildcard,
    Binder(PIdent),
    Bool(bool),
    Or(Box<[Pattern<'tcx>]>),
}

impl<'tcx> Pattern<'tcx> {
    pub(crate) fn span(mut self, sp: Span) -> Self {
        self.span = sp;
        self
    }

    pub(crate) fn bool(tcx: TyCtxt<'tcx>, b: bool) -> Self {
        Pattern { ty: tcx.types.bool, kind: PatternKind::Bool(b), span: DUMMY_SP }
    }

    pub(crate) fn wildcard(ty: Ty<'tcx>) -> Self {
        Pattern { ty, kind: PatternKind::Wildcard, span: DUMMY_SP }
    }

    pub(crate) fn binder(x: impl Into<PIdent>, ty: Ty<'tcx>) -> Self {
        Pattern { ty, kind: PatternKind::Binder(x.into()), span: DUMMY_SP }
    }

    pub(crate) fn binder_sp(x: impl Into<PIdent>, span: Span, ty: Ty<'tcx>) -> Self {
        Pattern { ty, kind: PatternKind::Binder(x.into()), span }
    }

    pub(crate) fn deref(self, ty: Ty<'tcx>) -> Self {
        Pattern { ty, span: self.span, kind: PatternKind::Deref(Box::new(self)) }
    }

    pub(crate) fn constructor(
        variant: VariantIdx,
        fields: impl IntoIterator<Item = (FieldIdx, Pattern<'tcx>)>,
        ty: Ty<'tcx>,
    ) -> Self {
        Pattern {
            ty,
            kind: PatternKind::Constructor(variant, fields.into_iter().collect()),
            span: DUMMY_SP,
        }
    }

    pub(crate) fn tuple(fields: impl IntoIterator<Item = Pattern<'tcx>>, ty: Ty<'tcx>) -> Self {
        Pattern { ty, kind: PatternKind::Tuple(fields.into_iter().collect()), span: DUMMY_SP }
    }

    pub(crate) fn get_bool(&self) -> Option<bool> {
        match self.kind {
            PatternKind::Bool(b) => Some(b),
            _ => None,
        }
    }

    pub(crate) fn rename_binds(
        &mut self,
        binders: &mut HashMap<Ident, Ident>,
        seen: &mut HashSet<Ident>,
    ) {
        match &mut self.kind {
            PatternKind::Constructor(_, fields) => {
                fields.iter_mut().for_each(|(_, f)| f.rename_binds(binders, seen))
            }
            PatternKind::Tuple(fields) => {
                fields.iter_mut().for_each(|f| f.rename_binds(binders, seen))
            }
            PatternKind::Wildcard => {}
            PatternKind::Binder(s) => {
                if seen.contains(&s.0) {
                    s.0 = binders[&s.0]
                } else {
                    let new_ident = s.0.refresh();
                    binders.insert(s.0, new_ident);
                    seen.insert(s.0);
                    s.0 = new_ident
                }
            }
            PatternKind::Bool(_) => {}
            PatternKind::Deref(pointee) => pointee.rename_binds(binders, seen),
            PatternKind::Or(patterns) => {
                patterns.iter_mut().for_each(|p| p.rename_binds(binders, seen))
            }
        }
    }

    pub(crate) fn binds(&self, binders: &mut HashSet<Ident>) {
        match &self.kind {
            PatternKind::Constructor(_, fields) => {
                fields.iter().for_each(|(_, f)| f.binds(binders))
            }
            PatternKind::Tuple(fields) => fields.iter().for_each(|f| f.binds(binders)),
            PatternKind::Wildcard => {}
            PatternKind::Binder(s) => {
                binders.insert(s.0);
            }
            PatternKind::Bool(_) => {}
            PatternKind::Deref(pointee) => pointee.binds(binders),
            PatternKind::Or(patterns) => patterns.iter().for_each(|f| f.binds(binders)),
        }
    }
}

const TRIGGER_ERROR: &str = "Triggers can only be used inside quantifiers";

/// Get a Pearlite term together with its free variables.
pub(crate) fn pearlite<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: LocalDefId,
) -> CreusotResult<(Box<[(PIdent, Ty<'tcx>)]>, Term<'tcx>)> {
    let (bound, triggers, term) = pearlite_with_triggers(ctx, id)?;
    if !triggers.is_empty() {
        Err(Error::msg(ctx.def_span(id), TRIGGER_ERROR))
    } else {
        Ok((bound, term))
    }
}

fn pearlite_with_triggers<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: LocalDefId,
) -> CreusotResult<(Box<[(PIdent, Ty<'tcx>)]>, Box<[Trigger<'tcx>]>, Term<'tcx>)> {
    let did = id.into();
    let Some((thir, expr)) = ctx.get_local_thir(id) else { return Err(Error::ErrorGuaranteed) };
    let lower = ThirTerm { ctx, item_id: id, thir };

    let (triggers, body) = lower.body_term(*expr)?;

    // All that remains is to translate patterns in the parameter list.
    // Postconditions make this annoying. They are closures with a `result` parameter,
    // so we have to collect the parameters of the parent function and the current closure.
    let to_pattern = |param: &thir::Param<'tcx>| {
        param.pat.as_ref().map(|box pat| lower.pattern_term(ctx, pat, true))
    };
    let is_closure = ctx.is_closure_like(did);
    let patterns: Box<[Pattern]> = if is_spec(ctx.tcx, did) && is_closure {
        // Most specs are closures.
        // Preconditions and variants have all of their variables bound in the parent function.
        // Postconditions also bind a `result` variable.
        let parent = ctx.parent(did).expect_local();
        let Some((parent_thir, _)) = ctx.get_local_thir(parent) else {
            return Err(Error::ErrorGuaranteed);
        };
        // Parameters of the parent function plus maybe the `result` parameter from the current closure
        parent_thir
            .params
            .iter()
            .chain(thir.params.iter().skip(1))
            .filter_map(to_pattern)
            .collect::<CreusotResult<_>>()
    } else if is_logic_closure(ctx.tcx, did) {
        // Skip implicit `self` parameter, and remove the & pattern which is sometimes
        // added for parameters of mappings.
        // In other cases, binders are just variables and they are left intact.
        // The only case where users can write arbitrary patterns in closure binders is
        // the one where the desugaring wraps it in `&`, so there is no risk of removing
        // a user-written `&` here.
        thir.params
            .iter()
            .skip(1)
            .filter_map(to_pattern)
            .map(|pat| {
                pat.map(|pat| match pat.kind {
                    PatternKind::Deref(pat) => *pat,
                    _ => pat,
                })
            })
            .collect::<CreusotResult<_>>()
    } else {
        assert!(!is_closure);
        // Case of non-specs or trait item specs (which desugar to extra trait items).
        thir.params.iter().filter_map(to_pattern).collect::<CreusotResult<_>>()
    }?;
    let bound: Box<[(PIdent, Ty<'tcx>)]> = patterns
        .iter()
        .enumerate()
        .map(|(idx, pat)| {
            let ident = match pat.kind {
                PatternKind::Binder(var) => var,
                _ => Ident::fresh_local(format!("__{}", idx)).into(),
            };
            (
                ident,
                ctx.normalize_erasing_regions(TypingEnv::non_body_analysis(ctx.tcx, did), pat.ty),
            )
        })
        .collect();
    let body = patterns.into_iter().zip(bound.iter().cloned()).rev().fold(
        body,
        |body: Term<'tcx>, (pattern, (ident, ty))| match pattern.kind {
            PatternKind::Binder(_) | PatternKind::Wildcard => body,
            _ => {
                let span = body.span;
                Term::let_(pattern, Term::var(ident, ty), body).span(span)
            }
        },
    );
    Ok((bound, triggers, body))
}

struct ThirTerm<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    item_id: LocalDefId,
    thir: &'a Thir<'tcx>,
}

// TODO: Ensure that types are correct during this translation, in particular
// - Box, & and &mut
impl<'tcx> ThirTerm<'_, 'tcx> {
    fn body_term(&self, expr: ExprId) -> CreusotResult<(Box<[Trigger<'tcx>]>, Term<'tcx>)> {
        let mut triggers = vec![];
        let expr = self.collect_triggers(expr, &mut triggers)?;
        let body = self.expr_term(expr)?;
        Ok((triggers.into(), body))
    }

    fn collect_triggers(
        &self,
        expr: ExprId,
        triggers: &mut Vec<Trigger<'tcx>>,
    ) -> CreusotResult<ExprId> {
        match self.unscope(expr).kind {
            ExprKind::Call { ty, ref args, .. } => {
                if let Some(Stub::Trigger) = pearlite_stub(self.ctx, ty) {
                    let trigger = self.expr_term(args[0])?;
                    if let TermKind::Tuple { fields } = trigger.kind {
                        triggers.push(Trigger(fields));
                        self.collect_triggers(args[1], triggers)
                    } else {
                        let span = self.thir[args[0]].span;
                        Err(Error::msg(span, "Triggers must be tuples"))
                    }
                } else {
                    Ok(expr)
                }
            }
            ExprKind::Block { block } => {
                if let Block { stmts: box [], expr: Some(expr), .. } = self.thir[block] {
                    self.collect_triggers(expr, triggers)
                } else {
                    Ok(expr)
                }
            }
            _ => Ok(expr),
        }
    }

    fn unscope(&self, expr: ExprId) -> &thir::Expr<'tcx> {
        match self.thir[expr] {
            thir::Expr { kind: ExprKind::Scope { value, .. }, .. } => self.unscope(value),
            ref r => r,
        }
    }

    fn rename(&self, id: HirId) -> PIdent {
        PIdent(self.ctx.rename(id))
    }

    /// Filter out `ensures`/`requires`, but keep `proof_assert`!
    fn not_spec(&self, id: StmtId) -> bool {
        match self.thir[id].kind {
            StmtKind::Expr { expr, .. } => self.not_spec_expr(expr),
            StmtKind::Let { initializer, .. } => {
                if let Some(initializer) = initializer {
                    self.not_spec_expr(initializer)
                } else {
                    true
                }
            }
        }
    }

    fn not_spec_expr(&self, id: ExprId) -> bool {
        match self.unscope(id).kind {
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                let closure_id = closure_id.to_def_id();
                !is_spec(self.ctx.tcx, closure_id) || is_assertion(self.ctx.tcx, closure_id)
            }
            _ => true,
        }
    }

    /// Translate a THIR expression into a term.
    fn expr_term(&self, expr: ExprId) -> CreusotResult<Term<'tcx>> {
        let thir::Expr { span, ty, ref kind, .. } = *self.unscope(expr);
        let res = match *kind {
            ExprKind::Block { block } => {
                let Block { ref stmts, expr, .. } = self.thir[block];
                let mut inner = match expr {
                    Some(e) => self.expr_term(e)?,
                    None => Term::unit(self.ctx.tcx).span(span),
                };
                for stmt in stmts.iter().rev().filter(|id| self.not_spec(**id)) {
                    inner = self.stmt_term(*stmt, inner)?;
                }
                Ok(inner)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.expr_term(lhs)?;
                let rhs = self.expr_term(rhs)?;

                use rustc_middle::mir::BinOp::*;
                let op = match op {
                    Add | AddUnchecked => BinOp::Add,
                    Sub | SubUnchecked => BinOp::Sub,
                    Mul | MulUnchecked => BinOp::Mul,
                    BitXor => BinOp::BitXor,
                    BitAnd => BinOp::BitAnd,
                    BitOr => BinOp::BitOr,
                    Shl | ShlUnchecked => BinOp::Shl,
                    Shr | ShrUnchecked => BinOp::Shr,
                    Lt => BinOp::Lt,
                    Le => BinOp::Le,
                    Ge => BinOp::Ge,
                    Gt => BinOp::Gt,
                    Div | Rem | Ne | Eq => unreachable!(),
                    Offset | Cmp | AddWithOverflow | SubWithOverflow | MulWithOverflow => {
                        return Err(Error::msg(span, "Unsupported binary operation {op}"));
                    }
                };
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Binary { op, lhs: Box::new(lhs), rhs: Box::new(rhs) },
                })
            }
            ExprKind::LogicalOp { op, lhs, rhs } => {
                let lhs = self.expr_term(lhs)?;
                let rhs = self.expr_term(rhs)?;
                let op = match op {
                    thir::LogicalOp::And => BinOp::And,
                    thir::LogicalOp::Or => BinOp::Or,
                };
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Binary { op, lhs: Box::new(lhs), rhs: Box::new(rhs) },
                })
            }
            ExprKind::Unary { op, arg } => {
                let arg = self.expr_term(arg)?;
                use rustc_middle::mir::UnOp::*;
                let op = match op {
                    Not => UnOp::Not,
                    Neg => UnOp::Neg,
                    PtrMetadata => {
                        return Err(Error::msg(span, "Unsupported unary operation {op}"));
                    }
                };
                Ok(Term { ty, span, kind: TermKind::Unary { op, arg: Box::new(arg) } })
            }
            ExprKind::VarRef { id } | ExprKind::UpvarRef { var_hir_id: id, .. } => {
                Ok(Term { ty, span, kind: TermKind::Var(self.rename(id.0)) })
            }
            ExprKind::Literal { lit, neg } => {
                let lit = match lit.node {
                    LitKind::Bool(b) => Literal::Bool(b),
                    LitKind::Int(u, lty) => {
                        let u = u.get();
                        match lty {
                            LitIntType::Signed(ity) => {
                                let val = if neg { (u as i128).wrapping_neg() } else { u as i128 };
                                Literal::MachSigned(val, ity)
                            }
                            LitIntType::Unsigned(uty) => Literal::MachUnsigned(u, uty),
                            LitIntType::Unsuffixed => match ty.kind() {
                                TyKind::Int(ity) => {
                                    let val =
                                        if neg { (u as i128).wrapping_neg() } else { u as i128 };
                                    Literal::MachSigned(val, *ity)
                                }
                                TyKind::Uint(uty) => Literal::MachUnsigned(u, *uty),
                                _ => unreachable!(),
                            },
                        }
                    }
                    LitKind::Char(c) => Literal::Char(c),
                    _ => self.ctx.dcx().span_bug(span, "Unsupported literal"),
                };
                Ok(Term { ty, span, kind: TermKind::Lit(lit) })
            }
            ExprKind::Call { ty: f_ty, ref args, fun, .. } => {
                use Stub::*;
                match pearlite_stub(self.ctx, f_ty) {
                    Some(s @ (Forall | Exists)) => {
                        let kind =
                            if let Forall = s { QuantKind::Forall } else { QuantKind::Exists };
                        let (binder, trigger, body) = self.quant_term(args[0])?;
                        Ok(body.quant(kind, binder, trigger).span(span))
                    }
                    Some(Impl) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;
                        Ok(lhs.implies(rhs).span(span))
                    }
                    Some(Equals) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;
                        Ok(lhs.eq(self.ctx.tcx, rhs).span(span))
                    }
                    Some(Neq) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;
                        Ok(lhs.bin_op(ty, BinOp::Ne, rhs).span(span))
                    }
                    Some(VariantCheck) => self.expr_term(args[0]),
                    Some(Old) => {
                        let term = self.expr_term(args[0])?;
                        Ok(Term { ty, span, kind: TermKind::Old { term: Box::new(term) } })
                    }
                    Some(ResultCheck) => Ok(Term::unit(self.ctx.tcx).span(span)),
                    Some(Dead) => Err(Error::msg(
                        span,
                        "The `dead` term can only be used for the body of trusted logical functions",
                    )),
                    Some(Trigger) => Err(Error::msg(
                        span,
                        "Triggers can only be used directly inside quantifiers",
                    )),
                    Some(SeqLiteral) => {
                        // SeqLiteral is generated by the `seq!` macro.
                        // A call must look like `seq_literal!(&[x,y,z])`.
                        let mut term = args[0];
                        // Peel off everything to get to the array literal
                        let items = loop {
                            match &self.unscope(term).kind {
                                ExprKind::PointerCoercion { source, .. } => term = *source,
                                ExprKind::Borrow { arg, .. } => term = *arg,
                                ExprKind::Deref { arg, .. } => term = *arg,
                                ExprKind::Array { fields } => {
                                    break fields
                                        .iter()
                                        .map(|&item| self.expr_term(item))
                                        .collect::<CreusotResult<_>>()?;
                                }
                                _ => {
                                    return Err(Error::msg(
                                        span,
                                        "Bad seq! This should not happen.",
                                    ));
                                }
                            }
                        };
                        Ok(Term { kind: TermKind::SeqLiteral(items), ty, span })
                    }
                    None => {
                        let fun = self.expr_term(fun)?;
                        let TermKind::Item(id, subst) = fun.kind else {
                            unreachable!("Call on non-function type");
                        };
                        // Allow dereferencing of `Ghost` in pearlite
                        if self.ctx.is_diagnostic_item(sym::deref_method, id)
                            && let Some(adt) = subst.type_at(0).ty_adt_def()
                            && Intrinsic::Ghost.is(self.ctx, adt.did())
                        {
                            Ok(self.expr_term(args[0])?.coerce(ty).span(span))
                        } else {
                            let args: Box<[_]> = args
                                .iter()
                                .map(|arg| self.expr_term(*arg))
                                .collect::<Result<_, _>>()?;
                            Ok(Term::call_no_normalize(self.ctx.tcx, id, subst, args).span(span))
                        }
                    }
                }
            }
            ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } => {
                Ok(self.expr_term(arg)?.coerce(ty).span(span))
            }
            ExprKind::Borrow { arg, .. } => {
                Ok(Term { ty, span, kind: self.logical_reborrow(arg)? })
            }
            ExprKind::Adt(box AdtExpr {
                adt_def,
                variant_index,
                ref fields,
                ref base,
                args,
                ..
            }) => {
                let mut fields: Vec<_> = fields
                    .iter()
                    .map(|f| Ok((f.name, self.expr_term(f.expr)?)))
                    .collect::<Result<_, Error>>()?;

                match base {
                    thir::AdtExprBase::None => (),
                    thir::AdtExprBase::Base(base) => {
                        let variant = &adt_def.variant(variant_index);

                        let base = self.expr_term(base.base)?;
                        let missing: Vec<_> = (0..variant.fields.len())
                            .filter(|i| !fields.iter().any(|(f, _)| i == &f.as_usize()))
                            .collect();

                        for missing_field in missing {
                            let missing_field: FieldIdx = missing_field.into();
                            fields.push((
                                missing_field,
                                base.clone().proj(
                                    missing_field,
                                    variant.fields[missing_field].ty(self.ctx.tcx, args),
                                ),
                            ));
                        }
                    }
                    thir::AdtExprBase::DefaultFields(_) => {
                        return Err(Error::msg(
                            span,
                            "Default field values syntax is not supported in pearlite",
                        ));
                    }
                }

                fields.sort_by_key(|f| f.0);

                let fields = fields.into_iter().map(|f| f.1).collect();
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Constructor { variant: variant_index, fields },
                })
            }
            // `*&expr` is identical to `expr` in Pearlite
            ExprKind::Deref { arg }
                if let ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } =
                    self.unscope(arg).kind =>
            {
                self.expr_term(arg)
            }
            ExprKind::Deref { arg }
                if let ExprKind::Call { ty, ref args, .. } = self.unscope(arg).kind
                    && let &TyKind::FnDef(f_did, subst) = ty.kind()
                    && self.ctx.is_diagnostic_item(sym::deref_mut_method, f_did)
                    && let ExprKind::Borrow { borrow_kind, arg } = self.unscope(args[0]).kind =>
            {
                // We have just detected `*deref_mut(&mut x)`, which can happen only for Ghost and Snapshot
                assert_matches!(borrow_kind, BorrowKind::Mut { .. });
                assert_matches!(subst.type_at(0).kind(),
                    TyKind::Adt(adt, _) if matches!(self.ctx.intrinsic(adt.did()), Intrinsic::Snapshot | Intrinsic::Ghost));
                Ok(self.expr_term(arg)?.coerce(ty).span(span))
            }
            ExprKind::Deref { arg } => Ok(self.expr_term(arg)?.deref().span(span)),
            ExprKind::Match { scrutinee, ref arms, .. } => {
                let scrutinee = self.expr_term(scrutinee)?;
                if arms.is_empty() {
                    return Err(Error::msg(
                        span,
                        "Empty matches are forbidden in Pearlite, because Why3 types are always inhabited.",
                    ));
                }
                let arms =
                    arms.iter().map(|arm| self.arm_term(*arm)).collect::<Result<Vec<_>, _>>()?;
                Ok(scrutinee.match_(arms).span(span))
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                let cond = self.expr_term(cond)?;
                let then = self.expr_term(then)?;
                let els = if let Some(els) = else_opt {
                    self.expr_term(els)?
                } else {
                    Term::unit(self.ctx.tcx).span(span)
                };
                Ok(cond
                    .match_([
                        (Pattern::bool(self.ctx.tcx, true), then),
                        (Pattern::bool(self.ctx.tcx, false), els),
                    ])
                    .span(span))
            }
            ExprKind::Field { lhs, name, .. } => {
                let lhs = self.expr_term(lhs)?;
                Ok(lhs.proj(name, ty).span(span))
            }
            ExprKind::Tuple { ref fields } => {
                let fields = fields.iter().map(|f| self.expr_term(*f)).collect::<Result<_, _>>()?;
                Ok(Term { ty, span, kind: TermKind::Tuple { fields } })
            }
            ExprKind::Use { source } => self.expr_term(source),
            ExprKind::ValueTypeAscription { source, .. } => self.expr_term(source),
            ExprKind::Box { value } => self.expr_term(value),
            ExprKind::NonHirLiteral { .. } => match ty.kind() {
                TyKind::FnDef(id, substs) => Ok(Term::item(*id, substs, ty).span(span)),
                _ => Err(Error::msg(span, "unhandled literal expression")),
            },
            ExprKind::NamedConst { def_id, args, .. } => Ok(Term::item(def_id, args, ty)),
            ExprKind::ZstLiteral { .. } => match ty.kind() {
                TyKind::FnDef(def_id, subst) => Ok(Term::item(*def_id, subst, ty)),
                _ => Ok(Term { ty, span, kind: TermKind::Lit(Literal::ZST) }),
            },
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                let (bound, term) = pearlite(self.ctx, closure_id)?;

                if is_assertion(self.ctx.tcx, closure_id.to_def_id()) {
                    Ok(Term { ty, span, kind: TermKind::Assert { cond: Box::new(term) } })
                } else {
                    Ok(Term { ty, span, kind: TermKind::Closure { bound, body: Box::new(term) } })
                }
            }
            ExprKind::Cast { source } => {
                let source = self.expr_term(source)?;
                Ok(Term { ty, span, kind: TermKind::Cast { arg: Box::new(source) } })
            }
            ExprKind::NeverToAny { source } => {
                // When the cast comes from an empty match, prefer the error message
                // from the empty match. It is more helpful because it has a visible source.
                let _ = self.expr_term(source)?;
                Err(Error::msg(
                    span,
                    "Casts from ! are not supported in Pearlite, because Why3 types are always inhabited.",
                ))
            }
            ExprKind::PointerCoercion {
                cast: PointerCoercion::MutToConstPointer, source, ..
            } => Ok(self.expr_term(source)?.coerce(ty).span(span)),
            ExprKind::ConstParam { param, def_id: _ } => {
                Ok(Term::const_param(self.ctx.tcx, param, ty, span))
            }
            ref ek => Err(Error::msg(span, format!("Unsupported expression kind {:?}", ek))),
        };
        Ok(Term { ty, ..res? })
    }

    fn arm_term(&self, arm: ArmId) -> CreusotResult<(Pattern<'tcx>, Term<'tcx>)> {
        let arm = &self.thir[arm];

        if arm.guard.is_some() {
            return Err(Error::msg(arm.span, "match guards are unsupported"));
        }

        let pattern = self.pattern_term(self.ctx, &arm.pattern, false)?;
        let body = self.expr_term(arm.body)?;

        Ok((pattern, body))
    }

    fn pattern_term(
        &self,
        ctx: &TranslationCtx<'tcx>,
        pat: &Pat<'tcx>,
        mut_allowed: bool,
    ) -> CreusotResult<Pattern<'tcx>> {
        trace!("{:?}", pat);
        match &pat.kind {
            PatKind::Wild => {
                Ok(Pattern { ty: pat.ty, span: pat.span, kind: PatternKind::Wildcard })
            }
            PatKind::Binding { mode, var, .. } => {
                if mode.0 == ByRef::Yes(Mutability::Mut) {
                    return Err(Error::msg(
                        pat.span,
                        "mut ref binders are not supported in pearlite",
                    ));
                }
                if !mut_allowed && mode.1 == Mutability::Mut {
                    return Err(Error::msg(pat.span, "mut binders are not supported in pearlite"));
                }
                let ident = self.rename(var.0);
                Ok(Pattern { ty: pat.ty, span: pat.span, kind: PatternKind::Binder(ident) })
            }
            PatKind::Variant { subpatterns, variant_index, .. } => {
                let fields = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, self.pattern_term(ctx, &pat.pattern, mut_allowed)?)))
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Pattern::constructor(*variant_index, fields, pat.ty).span(pat.span))
            }
            PatKind::Leaf { subpatterns } => {
                let fields = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, self.pattern_term(ctx, &pat.pattern, mut_allowed)?)))
                    .collect::<Result<Vec<_>, Error>>()?;

                if let TyKind::Tuple(_) = pat.ty.kind() {
                    Ok(Pattern::tuple(fields.into_iter().map(|a| a.1), pat.ty).span(pat.span))
                } else {
                    Ok(Pattern::constructor(VariantIdx::ZERO, fields, pat.ty).span(pat.span))
                }
            }
            PatKind::Deref { subpattern }
            | PatKind::DerefPattern { subpattern, borrow: ByRef::No } => Ok(Pattern {
                ty: pat.ty,
                span: pat.span,
                kind: PatternKind::Deref(Box::new(self.pattern_term(
                    ctx,
                    subpattern,
                    mut_allowed,
                )?)),
            }),
            PatKind::Constant { value } => {
                if !pat.ty.is_bool() {
                    return Err(Error::msg(
                        pat.span,
                        "non-boolean constant patterns are unsupported",
                    ));
                }
                Ok(Pattern {
                    ty: pat.ty,
                    span: pat.span,
                    kind: PatternKind::Bool(value.try_to_bool().unwrap()),
                })
            }
            // TODO: this simply ignores type annotations, maybe we should actually support them
            PatKind::AscribeUserType { ascription: _, subpattern } => {
                self.pattern_term(ctx, subpattern, mut_allowed)
            }
            PatKind::Or { pats } => {
                let pats = pats
                    .iter()
                    .map(|pat| self.pattern_term(ctx, &pat, mut_allowed))
                    .collect::<Result<Box<[_]>, Error>>()?;
                Ok(Pattern { ty: pat.ty, span: pat.span, kind: PatternKind::Or(pats) })
            }
            ref pk => ctx.dcx().span_bug(pat.span, format!("Unsupported pattern kind {:?}", pk)),
        }
    }

    fn stmt_term(&self, stmt: StmtId, inner: Term<'tcx>) -> CreusotResult<Term<'tcx>> {
        match &self.thir[stmt].kind {
            StmtKind::Expr { expr, .. } => {
                let arg = self.expr_term(*expr)?;
                if let TermKind::Tuple { fields } = &arg.kind {
                    if fields.is_empty() {
                        return Ok(inner);
                    }
                };
                let span = self.thir[*expr].span;
                Ok(Term::let_(Pattern::wildcard(arg.ty), arg, inner).span(span))
            }
            StmtKind::Let { pattern, initializer, init_scope, .. } => {
                let pattern = self.pattern_term(self.ctx, pattern, false)?;
                if let Some(initializer) = initializer {
                    let initializer = self.expr_term(*initializer)?;
                    let span =
                        init_scope.span(self.ctx.tcx, self.ctx.region_scope_tree(self.item_id));
                    Ok(Term::let_(pattern, initializer, inner).span(span))
                } else {
                    let span = self.ctx.hir_span(HirId {
                        owner: OwnerId { def_id: self.item_id },
                        local_id: init_scope.local_id,
                    });
                    Err(Error::msg(span, "let-bindings must have values"))
                }
            }
        }
    }

    fn quant_term(
        &self,
        body: ExprId,
    ) -> CreusotResult<(Box<[(PIdent, Ty<'tcx>)]>, Box<[Trigger<'tcx>]>, Term<'tcx>)> {
        let e = self.unscope(body);
        trace!("{:?}", e.kind);
        match e.kind {
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                pearlite_with_triggers(self.ctx, closure_id)
            }
            _ => Err(Error::msg(e.span, "unexpected error in quantifier")),
        }
    }

    /// Creates a 'logical' reborrow of a mutable borrow.
    /// The idea is that the expression `&mut ** X` for `X: &mut &mut T` should produces a pearlite value of type `&mut T`.
    ///
    /// However, this also has to deal with the idea that `* X` access the current value of a borrow in Pearlite.
    /// In actuality `&mut ** X` and `*X` are the same thing in THIR (rather the second doesn't exist).
    /// This has a **notable** consequence: an hist_inving of a mutable borrow in Pearlite must be the same as its **current value**.
    /// That is: `Y = &mut ** X` means that `* Y = ** X` and `^ Y = ^* X`. This is **unlike** in programs in which the `^` and `*` are
    /// swapped. While this difference is not satisfactory, it is a natural consequence of the properties of a logic, in particular stability
    ///  under substitution. We are allowed to write the following in Pearlite:
    ///
    /// let a = * x;
    /// let b = &mut * a; // &mut cannot be writte in surface syntax.
    ///
    /// However we translate `&mut x` should be the same as if we had first substituted `a`.
    /// This is not fully satisfactory, but the other choice where we correspond to the behavior of programs is not stable under
    /// substitution.
    fn logical_reborrow(&self, rebor_id: ExprId) -> Result<TermKind<'tcx>, Error> {
        // Check for the simple `&mut * x` case (with x a mutable borrow).
        if let ExprKind::Deref { arg } = self.unscope(rebor_id).kind
            && let TyKind::Ref(_, _, Mutability::Mut) = self.thir[arg].ty.kind()
        {
            return Ok(self.expr_term(arg)?.kind);
        };

        // Handle every other case.
        let (inner, projections) = self.logical_reborrow_inner(rebor_id)?;
        Ok(TermKind::Reborrow { inner: Box::new(inner), projections: projections.into() })
    }

    fn logical_reborrow_inner(
        &self,
        rebor_id: ExprId,
    ) -> Result<(Term<'tcx>, Vec<ProjectionElem<Term<'tcx>, Ty<'tcx>>>), Error> {
        let thir::Expr { ty, span, ref kind, .. } = *self.unscope(rebor_id);
        match *kind {
            ExprKind::Block { block } => {
                let Block { stmts, expr, .. } = &self.thir[block];
                assert!(stmts.is_empty());
                return self.logical_reborrow_inner(expr.unwrap());
            }
            ExprKind::Field { lhs, name, .. } => {
                let (inner, mut proj) = self.logical_reborrow_inner(lhs)?;
                proj.push(ProjectionElem::Field(name, ty));
                return Ok((inner, proj));
            }
            ExprKind::Deref { arg } => match self.thir[arg].ty.kind() {
                TyKind::Ref(_, _, Mutability::Mut) => {
                    let inner = self.expr_term(arg)?;
                    return Ok((inner.span(span), Vec::new()));
                }
                TyKind::Ref(_, _, Mutability::Not)
                    if let ExprKind::Call { ty, ref args, .. } = self.unscope(arg).kind
                        && let &TyKind::FnDef(f_did, subst) = ty.kind()
                        && self.ctx.is_diagnostic_item(sym::deref_method, f_did)
                        && let ExprKind::Borrow { borrow_kind, arg } =
                            self.unscope(args[0]).kind =>
                {
                    // We have just detected * deref &. Treat it as nop.
                    assert_matches!(borrow_kind, BorrowKind::Shared);
                    assert_matches!(subst.type_at(0).kind(),
                        TyKind::Adt(adt, _) if matches!(self.ctx.intrinsic(adt.did()), Intrinsic::Snapshot | Intrinsic::Ghost));
                    return self.logical_reborrow_inner(arg);
                }
                TyKind::Adt(adtdef, _) if adtdef.is_box() => {
                    let mut res = self.logical_reborrow_inner(arg)?;
                    res.1.push(ProjectionElem::Deref);
                    return Ok(res);
                }
                _ => (),
            },
            ExprKind::Call { ty: fn_ty, ref args, .. }
                if let TyKind::FnDef(id, _) = fn_ty.kind()
                    && Intrinsic::IndexLogic.is(self.ctx, *id) =>
            {
                if !matches!(
                    self.thir[args[0]].ty.kind(),
                    TyKind::Str | TyKind::Array(_, _) | TyKind::Slice(_)
                ) {
                    return Err(Error::msg(
                        span,
                        format!(
                            "Unsupported logical reborrow of indexing, only slice indexing is supported"
                        ),
                    ));
                }

                let (inner, mut proj) = self.logical_reborrow_inner(args[0])?;
                proj.push(ProjectionElem::Index(self.expr_term(args[1])?));
                return Ok((inner, proj));
            }
            _ => (),
        }

        Err(Error::msg(
            span,
            format!(
                "Unsupported logical reborrow, only field projections and slice indexing are supported"
            ),
        ))
    }
}

pub(crate) fn type_invariant_term<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ident: Ident,
    span: Span,
    ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    let args = Box::new([Term { ty, span, kind: TermKind::Var(ident.into()) }]);
    let (inv_fn_did, inv_fn_substs) = ctx.type_invariant(typing_env, ty, span)?;
    Some(Term {
        ty: ctx.types.bool,
        span,
        kind: TermKind::Call { id: inv_fn_did, subst: inv_fn_substs, args },
    })
}

#[derive(Debug)]
pub(crate) enum Stub {
    Forall,
    Exists,
    Trigger,
    Impl,
    Equals,
    Neq,
    VariantCheck,
    Old,
    ResultCheck,
    Dead,
    SeqLiteral,
}

pub(crate) fn pearlite_stub<'tcx>(ctx: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Option<Stub> {
    if let TyKind::FnDef(id, _) = *ty.kind() {
        match ctx.intrinsic(id) {
            Intrinsic::Forall => Some(Stub::Forall),
            Intrinsic::Exists => Some(Stub::Exists),
            Intrinsic::Trigger => Some(Stub::Trigger),
            Intrinsic::Implication => Some(Stub::Impl),
            Intrinsic::Equal => Some(Stub::Equals),
            Intrinsic::Neq => Some(Stub::Neq),
            Intrinsic::VariantCheck => Some(Stub::VariantCheck),
            Intrinsic::Old => Some(Stub::Old),
            Intrinsic::Dead => Some(Stub::Dead),
            Intrinsic::ClosureResult => Some(Stub::ResultCheck),
            Intrinsic::SeqLiteral => Some(Stub::SeqLiteral),
            _ => None,
        }
    } else {
        None
    }
}

pub trait TermVisitor<'tcx>: Sized {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        super_visit_term(term, self);
    }

    #[allow(dead_code)] // TODO: not checking patterns causes `opacity.rs` to be overly permissive
    fn visit_pattern(&mut self, pat: &Pattern<'tcx>) {
        super_visit_pattern(pat, self);
    }
}

pub fn super_visit_term<'tcx, V: TermVisitor<'tcx>>(term: &Term<'tcx>, visitor: &mut V) {
    match &term.kind {
        TermKind::Var(_) | TermKind::Lit(_) => (),
        TermKind::SeqLiteral(fields) => fields.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Cast { arg } => visitor.visit_term(arg),
        TermKind::Coerce { arg } => visitor.visit_term(arg),
        TermKind::Item(_, _) | TermKind::Const(_) => {}
        TermKind::Binary { op: _, lhs, rhs } => {
            visitor.visit_term(lhs);
            visitor.visit_term(rhs);
        }
        TermKind::Unary { op: _, arg } => visitor.visit_term(arg),
        TermKind::Quant { body, trigger, .. } => {
            trigger.iter().flat_map(|x| &x.0).for_each(|x| visitor.visit_term(x));
            visitor.visit_term(body)
        }
        TermKind::Call { id: _, subst: _, args } => args.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Constructor { variant: _, fields } => {
            fields.iter().for_each(|a| visitor.visit_term(a))
        }
        TermKind::Tuple { fields } => fields.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Cur { term } => visitor.visit_term(term),
        TermKind::Fin { term } => visitor.visit_term(term),
        TermKind::Impl { lhs, rhs } => {
            visitor.visit_term(lhs);
            visitor.visit_term(rhs)
        }
        TermKind::Match { scrutinee, arms } => {
            visitor.visit_term(scrutinee);
            arms.iter().for_each(|(_pattern, arm)| {
                // visitor.visit_pattern(pattern); // Issue #1672
                visitor.visit_term(arm)
            })
        }
        TermKind::Let { pattern: _, arg, body } => {
            // visitor.visit_pattern(pattern); // Issue #1672
            visitor.visit_term(arg);
            visitor.visit_term(body)
        }
        TermKind::Projection { lhs, idx: _ } => visitor.visit_term(lhs),
        TermKind::Old { term } => visitor.visit_term(term),
        TermKind::Closure { body, .. } => visitor.visit_term(body),
        TermKind::Reborrow { inner, projections } => {
            visitor.visit_term(inner);
            visit_projections(projections, |term| visitor.visit_term(term))
        }
        TermKind::Assert { cond } => visitor.visit_term(cond),
        TermKind::Precondition { params, .. } => params.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Postcondition { params, .. } => params.iter().for_each(|a| visitor.visit_term(a)),
    }
}

pub fn super_visit_pattern<'tcx, V: TermVisitor<'tcx>>(pattern: &Pattern<'tcx>, visitor: &mut V) {
    match &pattern.kind {
        PatternKind::Constructor(_, patterns) => {
            patterns.iter().for_each(|(_, p)| visitor.visit_pattern(p))
        }
        PatternKind::Deref(pattern) => visitor.visit_pattern(pattern),
        PatternKind::Tuple(patterns) => patterns.iter().for_each(|p| visitor.visit_pattern(p)),
        PatternKind::Wildcard | PatternKind::Binder(_) | PatternKind::Bool(_) => (),
        PatternKind::Or(patterns) => patterns.iter().for_each(|p| visitor.visit_pattern(p)),
    }
}

pub trait TermVisitorMut<'tcx>: Sized {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
    }
}

pub(crate) fn super_visit_mut_term<'tcx, V: TermVisitorMut<'tcx>>(
    term: &mut Term<'tcx>,
    visitor: &mut V,
) {
    match &mut term.kind {
        TermKind::Var(_) | TermKind::Lit(_) => (),
        TermKind::SeqLiteral(fields) => fields.iter_mut().for_each(|a| visitor.visit_mut_term(a)),
        TermKind::Cast { arg } => visitor.visit_mut_term(&mut *arg),
        TermKind::Coerce { arg } => visitor.visit_mut_term(arg),
        TermKind::Item(..) | TermKind::Const(_) => {}
        TermKind::Binary { lhs, rhs, .. } => {
            visitor.visit_mut_term(&mut *lhs);
            visitor.visit_mut_term(&mut *rhs);
        }
        TermKind::Unary { arg, .. } => visitor.visit_mut_term(&mut *arg),
        TermKind::Quant { body, trigger, .. } => {
            trigger.iter_mut().flat_map(|x| &mut x.0).for_each(|x| visitor.visit_mut_term(x));
            visitor.visit_mut_term(&mut *body)
        }
        TermKind::Call { args, .. } => {
            args.iter_mut().for_each(|a| visitor.visit_mut_term(&mut *a))
        }
        TermKind::Constructor { fields, .. } => {
            fields.iter_mut().for_each(|a| visitor.visit_mut_term(&mut *a))
        }
        TermKind::Tuple { fields } => {
            fields.iter_mut().for_each(|a| visitor.visit_mut_term(&mut *a))
        }
        TermKind::Cur { term } => visitor.visit_mut_term(&mut *term),
        TermKind::Fin { term } => visitor.visit_mut_term(&mut *term),
        TermKind::Impl { lhs, rhs } => {
            visitor.visit_mut_term(&mut *lhs);
            visitor.visit_mut_term(&mut *rhs)
        }
        TermKind::Match { scrutinee, arms } => {
            visitor.visit_mut_term(&mut *scrutinee);
            arms.iter_mut().for_each(|(_pattern, arm)| {
                // visitor.visit_mut_pattern(pattern); // Issue #1672
                visitor.visit_mut_term(&mut *arm)
            })
        }
        TermKind::Let { pattern: _, arg, body } => {
            // visitor.visit_mut_pattern(pattern); // Issue #1672
            visitor.visit_mut_term(&mut *arg);
            visitor.visit_mut_term(&mut *body)
        }
        TermKind::Projection { lhs, idx: _ } => visitor.visit_mut_term(&mut *lhs),
        TermKind::Old { term } => visitor.visit_mut_term(&mut *term),
        TermKind::Closure { body, .. } => visitor.visit_mut_term(&mut *body),
        TermKind::Reborrow { inner, projections } => {
            visitor.visit_mut_term(&mut *inner);
            visit_projections_mut(projections, |term| visitor.visit_mut_term(term))
        }
        TermKind::Assert { cond } => visitor.visit_mut_term(&mut *cond),
        TermKind::Precondition { params, .. } => {
            params.iter_mut().for_each(|a| visitor.visit_mut_term(a))
        }
        TermKind::Postcondition { params, .. } => {
            params.iter_mut().for_each(|a| visitor.visit_mut_term(a))
        }
    }
}

impl<'tcx> Term<'tcx> {
    pub(crate) fn let_(pattern: Pattern<'tcx>, arg: Term<'tcx>, body: Term<'tcx>) -> Self {
        Term {
            span: pattern.span.until(body.span),
            ty: body.ty,
            kind: TermKind::Let { pattern, arg: Box::new(arg), body: Box::new(body) },
        }
    }

    pub(crate) fn match_(
        self,
        arms: impl IntoIterator<Item = (Pattern<'tcx>, Term<'tcx>)>,
    ) -> Self {
        let arms = arms.into_iter().collect::<Box<[_]>>();
        Term {
            ty: arms[0].1.ty.clone(),
            kind: TermKind::Match { scrutinee: Box::new(self), arms },
            span: DUMMY_SP,
        }
    }

    pub(crate) fn unit(tcx: TyCtxt<'tcx>) -> Self {
        Term { ty: tcx.types.unit, kind: TermKind::Tuple { fields: Box::new([]) }, span: DUMMY_SP }
    }

    pub(crate) fn true_(tcx: TyCtxt<'tcx>) -> Self {
        Term { ty: tcx.types.bool, kind: TermKind::Lit(Literal::Bool(true)), span: DUMMY_SP }
    }

    pub(crate) fn false_(tcx: TyCtxt<'tcx>) -> Self {
        Term { ty: tcx.types.bool, kind: TermKind::Lit(Literal::Bool(false)), span: DUMMY_SP }
    }

    pub(crate) fn proj(self, idx: FieldIdx, ty: Ty<'tcx>) -> Self {
        Term { ty, span: self.span, kind: TermKind::Projection { lhs: Box::new(self), idx } }
    }

    pub(crate) fn tuple(tcx: TyCtxt<'tcx>, fields: impl IntoIterator<Item = Term<'tcx>>) -> Self {
        let fields: Box<[_]> = fields.into_iter().collect();
        let mut span = DUMMY_SP;
        let ty = Ty::new_tup_from_iter(
            tcx,
            fields.iter().map(|t| {
                span = span.until(t.span);
                t.ty
            }),
        );
        Term { ty, kind: TermKind::Tuple { fields }, span }
    }

    pub(crate) fn call_no_normalize(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        subst: GenericArgsRef<'tcx>,
        args: impl IntoIterator<Item = Term<'tcx>>,
    ) -> Self {
        let ty = tcx.type_of(def_id).instantiate(tcx, subst);
        let result = tcx.instantiate_bound_regions_with_erased(ty.fn_sig(tcx).output());
        let args = args.into_iter().collect();
        Term { ty: result, span: DUMMY_SP, kind: TermKind::Call { id: def_id, subst, args } }
    }

    pub(crate) fn call(
        tcx: TyCtxt<'tcx>,
        typing_env: TypingEnv<'tcx>,
        def_id: DefId,
        subst: GenericArgsRef<'tcx>,
        args: impl IntoIterator<Item = Term<'tcx>>,
    ) -> Self {
        let mut res = Self::call_no_normalize(tcx, def_id, subst, args);
        res.ty = tcx.normalize_erasing_regions(typing_env, res.ty);
        res
    }

    pub(crate) fn var(ident: impl Into<PIdent>, ty: Ty<'tcx>) -> Self {
        Term { ty, kind: TermKind::Var(ident.into()), span: DUMMY_SP }
    }

    pub(crate) fn cur(self) -> Self {
        assert!(self.ty.is_mutable_ptr() && self.ty.is_ref(), "cannot cur type {:?}", self.ty);

        Term {
            ty: self.ty.builtin_deref(false).unwrap(),
            span: self.span,
            kind: TermKind::Cur { term: Box::new(self) },
        }
    }

    pub(crate) fn fin(self) -> Self {
        assert!(self.ty.is_mutable_ptr() && self.ty.is_ref(), "cannot final type {:?}", self.ty);

        Term {
            ty: self.ty.builtin_deref(false).unwrap(),
            span: self.span,
            kind: TermKind::Fin { term: Box::new(self) },
        }
    }

    pub(crate) fn deref(self) -> Self {
        if self.ty.is_box() || self.ty.ref_mutability() == Some(Not) {
            let ty = self.ty.builtin_deref(false).unwrap();
            self.coerce(ty)
        } else {
            assert_matches!(self.ty.kind(), TyKind::Ref(_, _, Mutability::Mut));
            self.cur()
        }
    }

    pub(crate) fn conj(self, rhs: Self) -> Self {
        match self.kind {
            // ⟘ ∧ A = ⟘
            TermKind::Lit(Literal::Bool(false)) => self,
            // ⟙ ∧ A = A
            TermKind::Lit(Literal::Bool(true)) => rhs,
            _ => match rhs.kind {
                // A ∧ ⟘ = ⟘
                TermKind::Lit(Literal::Bool(false)) => rhs,
                // A ∧ ⟙ = A
                TermKind::Lit(Literal::Bool(true)) => self,
                _ => Term {
                    ty: self.ty,
                    span: self.span.until(rhs.span),
                    kind: TermKind::Binary {
                        op: BinOp::And,
                        lhs: Box::new(self),
                        rhs: Box::new(rhs),
                    },
                },
            },
        }
    }

    pub(crate) fn bin_op(self, ty: Ty<'tcx>, op: BinOp, rhs: Self) -> Self {
        Term {
            ty,
            span: self.span.until(rhs.span),
            kind: TermKind::Binary { op, lhs: Box::new(self), rhs: Box::new(rhs) },
        }
    }

    pub(crate) fn eq(self, tcx: TyCtxt<'tcx>, rhs: Self) -> Self {
        self.bin_op(tcx.types.bool, BinOp::Eq, rhs)
    }

    pub(crate) fn implies(self, rhs: Self) -> Self {
        // A → ⟙ = ⟙
        if let TermKind::Lit(Literal::Bool(true)) = rhs.kind {
            return rhs;
        }

        match self.kind {
            // ⟙ → A = A
            TermKind::Lit(Literal::Bool(true)) => rhs,
            // (⟘ → A) = ⟙
            TermKind::Lit(Literal::Bool(false)) => {
                Term { ty: self.ty, kind: TermKind::Lit(Literal::Bool(true)), span: self.span }
            }
            _ => Term {
                ty: self.ty,
                span: self.span.until(rhs.span),
                kind: TermKind::Impl { lhs: Box::new(self), rhs: Box::new(rhs) },
            },
        }
    }

    pub(crate) fn forall_trig(
        self,
        binder: (PIdent, Ty<'tcx>),
        trigger: Box<[Trigger<'tcx>]>,
    ) -> Self {
        self.quant(QuantKind::Forall, Box::new([binder]), trigger)
    }

    pub(crate) fn forall(self, binder: (PIdent, Ty<'tcx>)) -> Self {
        self.forall_trig(binder, Box::new([]))
    }

    pub(crate) fn exists(self, binder: (PIdent, Ty<'tcx>)) -> Self {
        self.quant(QuantKind::Exists, Box::new([binder]), Box::new([]))
    }

    pub(crate) fn quant(
        self,
        quant_kind: QuantKind,
        binder: QuantBinder<'tcx>,
        trigger: Box<[Trigger<'tcx>]>,
    ) -> Self {
        assert!(self.ty.is_bool());

        match (&self.kind, quant_kind) {
            // ∀ x . ⟙ = ⟙
            (TermKind::Lit(Literal::Bool(true)), QuantKind::Forall) => self,
            // ∃ x . ⟘ = ⟘
            (TermKind::Lit(Literal::Bool(false)), QuantKind::Exists) => self,
            _ => Term {
                ty: self.ty,
                span: self.span,
                kind: TermKind::Quant { kind: quant_kind, binder, body: Box::new(self), trigger },
            },
        }
    }

    pub(crate) fn coerce(self, ty: Ty<'tcx>) -> Self {
        Term { ty, span: self.span, kind: TermKind::Coerce { arg: Box::new(self) } }
    }

    pub(crate) fn shr_ref(self, tcx: TyCtxt<'tcx>) -> Self {
        let ty = self.ty;
        self.coerce(Ty::new_ref(tcx, tcx.lifetimes.re_erased, ty, Mutability::Not))
    }

    pub(crate) fn shr_deref(self) -> Self {
        let ty = self.ty;
        assert_eq!(ty.ref_mutability(), Some(Not));
        self.coerce(ty.builtin_deref(false).unwrap())
    }

    pub(crate) fn int(int_ty: Ty<'tcx>, int: i128) -> Self {
        Term { ty: int_ty, kind: TermKind::Lit(Literal::Integer(int)), span: DUMMY_SP }
    }

    pub(crate) fn item(def_id: DefId, subst: GenericArgsRef<'tcx>, ty: Ty<'tcx>) -> Self {
        Term { ty, kind: TermKind::Item(def_id, subst), span: DUMMY_SP }
    }

    pub(crate) fn const_(c: Const<'tcx>, ty: Ty<'tcx>, span: Span) -> Self {
        Term { ty, span, kind: TermKind::Const(c) }
    }

    pub(crate) fn const_param(
        tcx: TyCtxt<'tcx>,
        param: ParamConst,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Self {
        Term::const_(Const::new_param(tcx, param), ty, span)
    }

    pub(crate) fn span(mut self, sp: Span) -> Self {
        self.span = sp;
        self
    }

    /// For each `(var, term)` in `inv_subst`, replace `var` by `term` in `self` (as
    /// long as `var` is not bound).
    ///
    /// # Example
    ///
    /// If `inv_subst` containts `("x", 5)`:
    /// - If `self` is `x == 1`, `self.subst(inv_subst)` is `5 + 1`
    /// - If `self` is `forall<x> x == 1`, `self.subst(inv_subst)` is still `forall<x> x == 1`
    pub(crate) fn subst(&mut self, subst: &impl Subst<'tcx>) {
        self.subst_(&HashMap::new(), subst)
    }

    fn subst_(&mut self, bound: &HashMap<Ident, Ident>, subst: &impl Subst<'tcx>) {
        match &mut self.kind {
            TermKind::Var(v) => match bound.get(&v.0) {
                Some(w) => v.0 = *w,
                None if let Some(t) = subst.subst(v.0) => self.kind = t,
                None => {}
            },
            TermKind::Lit(_) => {}
            TermKind::SeqLiteral(fields) => fields.iter_mut().for_each(|a| a.subst_(bound, subst)),
            TermKind::Cast { arg } => arg.subst_(bound, subst),
            TermKind::Coerce { arg } => arg.subst_(bound, subst),
            TermKind::Item(_, _) | TermKind::Const(_) => {}
            TermKind::Binary { lhs, rhs, .. } => {
                lhs.subst_(bound, subst);
                rhs.subst_(bound, subst)
            }
            TermKind::Unary { arg, .. } => arg.subst_(bound, subst),
            TermKind::Quant { binder, trigger, body, kind: _ } => {
                let mut bound = bound.clone();
                for (ident, _) in binder {
                    let new_ident = ident.0.refresh();
                    bound.insert(ident.0, new_ident);
                    ident.0 = new_ident;
                }
                trigger.iter_mut().flat_map(|ts| &mut ts.0).for_each(|t| t.subst_(&bound, subst));
                body.subst_(&bound, subst);
            }
            TermKind::Call { args, .. } => args.iter_mut().for_each(|f| f.subst_(bound, subst)),
            TermKind::Constructor { fields, .. } => {
                fields.iter_mut().for_each(|f| f.subst_(bound, subst))
            }
            TermKind::Tuple { fields } => fields.iter_mut().for_each(|f| f.subst_(bound, subst)),
            TermKind::Cur { term } => term.subst_(bound, subst),
            TermKind::Fin { term } => term.subst_(bound, subst),
            TermKind::Impl { lhs, rhs } => {
                lhs.subst_(bound, subst);
                rhs.subst_(bound, subst)
            }
            TermKind::Match { scrutinee, arms } => {
                scrutinee.subst_(bound, subst);
                arms.iter_mut().for_each(|(pat, arm)| {
                    let mut bound = bound.clone();
                    pat.rename_binds(&mut bound, &mut HashSet::new());
                    arm.subst_(&bound, subst);
                })
            }
            TermKind::Let { pattern, arg, body } => {
                arg.subst_(bound, subst);
                let mut bound = bound.clone();
                pattern.rename_binds(&mut bound, &mut HashSet::new());
                body.subst_(&bound, subst);
            }
            TermKind::Projection { lhs, .. } => lhs.subst_(bound, subst),
            TermKind::Old { term } => term.subst_(bound, subst),
            TermKind::Closure { body, bound: bound_new } => {
                let mut bound = bound.clone();
                bound.extend(bound_new.iter_mut().map(|(ident, _)| {
                    let rnm = (ident.0, ident.0.refresh());
                    ident.0 = rnm.1;
                    rnm
                }));
                body.subst_(&bound, subst);
            }
            TermKind::Reborrow { inner, projections } => {
                inner.subst_(bound, subst);
                visit_projections_mut(projections, |term| term.subst_(bound, subst))
            }
            TermKind::Assert { cond } => cond.subst_(bound, subst),
            TermKind::Precondition { params, .. } => {
                params.iter_mut().for_each(|p| p.subst_(bound, subst))
            }
            TermKind::Postcondition { params, .. } => {
                params.iter_mut().for_each(|p| p.subst_(bound, subst))
            }
        }
    }

    pub(crate) fn free_vars(&self) -> HashSet<Ident> {
        let mut free = HashSet::new();
        self.free_vars_inner(&HashSet::new(), &mut free);
        free
    }

    fn free_vars_inner(&self, bound: &HashSet<Ident>, free: &mut HashSet<Ident>) {
        match &self.kind {
            TermKind::Var(v) => {
                if !bound.contains(&v.0) {
                    free.insert(v.0);
                }
            }
            TermKind::Lit(_) => {}
            TermKind::SeqLiteral(fields) => {
                fields.iter().for_each(|a| a.free_vars_inner(bound, free))
            }
            TermKind::Cast { arg } => arg.free_vars_inner(bound, free),
            TermKind::Coerce { arg } => arg.free_vars_inner(bound, free),
            TermKind::Item(_, _) | TermKind::Const(_) => {}
            TermKind::Binary { lhs, rhs, .. } => {
                lhs.free_vars_inner(bound, free);
                rhs.free_vars_inner(bound, free)
            }
            TermKind::Unary { arg, .. } => arg.free_vars_inner(bound, free),
            TermKind::Quant { binder, body, .. } => {
                let mut bound = bound.clone();
                for (ident, _) in binder {
                    bound.insert(ident.0);
                }

                body.free_vars_inner(&bound, free);
            }
            TermKind::Call { args, .. } => {
                for arg in args {
                    arg.free_vars_inner(bound, free);
                }
            }
            TermKind::Constructor { fields, .. } => {
                for field in fields {
                    field.free_vars_inner(bound, free);
                }
            }
            TermKind::Tuple { fields } => {
                for field in fields {
                    field.free_vars_inner(bound, free);
                }
            }
            TermKind::Cur { term } => term.free_vars_inner(bound, free),
            TermKind::Fin { term } => term.free_vars_inner(bound, free),
            TermKind::Impl { lhs, rhs } => {
                lhs.free_vars_inner(bound, free);
                rhs.free_vars_inner(bound, free)
            }
            TermKind::Match { scrutinee, arms } => {
                scrutinee.free_vars_inner(bound, free);
                for (pat, arm) in arms {
                    let mut bound = bound.clone();
                    pat.binds(&mut bound);
                    arm.free_vars_inner(&bound, free);
                }
            }
            TermKind::Let { pattern, arg, body } => {
                arg.free_vars_inner(bound, free);
                let mut bound = bound.clone();
                pattern.binds(&mut bound);
                body.free_vars_inner(&bound, free);
            }
            TermKind::Projection { lhs, .. } => lhs.free_vars_inner(bound, free),
            TermKind::Old { term } => term.free_vars_inner(bound, free),
            TermKind::Closure { body, bound: bound_new } => {
                let mut bound = bound.clone();
                bound.extend(bound_new.iter().map(|b| b.0.0));
                body.free_vars_inner(&bound, free);
            }
            TermKind::Reborrow { inner, projections } => {
                inner.free_vars_inner(bound, free);
                visit_projections(projections, |term| term.free_vars_inner(bound, free))
            }
            TermKind::Assert { cond } => cond.free_vars_inner(bound, free),
            TermKind::Precondition { params, .. } => {
                params.iter().for_each(|p| p.free_vars_inner(bound, free))
            }
            TermKind::Postcondition { params, .. } => {
                params.iter().for_each(|p| p.free_vars_inner(bound, free))
            }
        }
    }
}

pub(crate) trait Subst<'tcx> {
    fn subst(&self, id: Ident) -> Option<TermKind<'tcx>>;
}

/// A substitution from a mapping of `Ident` to `TermKind`.
pub type MapSubstitution<'tcx> = HashMap<Ident, TermKind<'tcx>>;

impl<'tcx> Subst<'tcx> for MapSubstitution<'tcx> {
    fn subst(&self, k: Ident) -> Option<TermKind<'tcx>> {
        self.get(&k).cloned()
    }
}

/// A renaming from `Ident` to `Ident` in a small array.
pub struct SmallRenaming<const N: usize>(pub [(Ident, Ident); N]);

impl<'tcx, const N: usize> Subst<'tcx> for SmallRenaming<N> {
    fn subst(&self, x: Ident) -> Option<TermKind<'tcx>> {
        self.0.iter().find(|&&(from, _)| from == x).map(|&(_, to)| TermKind::Var(to.into()))
    }
}

impl<'tcx, F: Fn(Ident) -> Option<TermKind<'tcx>>> Subst<'tcx> for F {
    fn subst(&self, id: Ident) -> Option<TermKind<'tcx>> {
        self(id)
    }
}

#[allow(dead_code)]
/// A debug printer for Thir which allows you to see a thir expression as a tree
struct PrintExpr<'a, 'tcx>(&'a Thir<'tcx>, ExprId);

impl Display for PrintExpr<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        print_thir_expr(f, self.0, self.1)
    }
}

#[allow(dead_code)]
fn print_thir_expr(fmt: &mut Formatter, thir: &Thir, expr_id: ExprId) -> std::fmt::Result {
    match &thir[expr_id].kind {
        ExprKind::Call { fun, args, .. } => {
            print_thir_expr(fmt, thir, *fun)?;
            write!(fmt, "(")?;
            for a in args.iter() {
                print_thir_expr(fmt, thir, *a)?;
                write!(fmt, ",")?;
            }
            write!(fmt, ")")?;
        }
        ExprKind::Deref { arg } => {
            write!(fmt, "* ")?;
            print_thir_expr(fmt, thir, *arg)?;
        }
        ExprKind::Borrow { borrow_kind, arg } => {
            match borrow_kind {
                BorrowKind::Shared => write!(fmt, "& ")?,
                BorrowKind::Fake(..) => write!(fmt, "&fake ")?,
                BorrowKind::Mut { .. } => write!(fmt, "&mut ")?,
            };

            print_thir_expr(fmt, thir, *arg)?;
        }
        ExprKind::Field { lhs, variant_index, name } => {
            print_thir_expr(fmt, thir, *lhs)?;
            let ty = thir[expr_id].ty;
            let (var_name, field_name) = match ty.kind() {
                TyKind::Adt(def, _) => {
                    let var = &def.variants()[*variant_index];
                    (var.name.to_string(), var.fields[*name].name.to_string())
                }
                TyKind::Tuple(_) => ("_".into(), format!("{name:?}")),
                _ => unreachable!(),
            };

            write!(fmt, " as {var_name} . {field_name}")?;
        }
        ExprKind::Index { lhs, index } => {
            print_thir_expr(fmt, thir, *lhs)?;
            write!(fmt, "[")?;
            print_thir_expr(fmt, thir, *index)?;
            write!(fmt, "]")?;
        }
        ExprKind::ZstLiteral { .. } => match thir[expr_id].ty.kind() {
            TyKind::FnDef(id, _) => write!(fmt, "{id:?}")?,
            _ => write!(fmt, "zst")?,
        },
        ExprKind::Literal { lit, neg } => {
            if *neg {
                write!(fmt, "-")?;
            }

            write!(fmt, "{}", lit.node)?;
        }
        ExprKind::Use { source } => print_thir_expr(fmt, thir, *source)?,
        ExprKind::VarRef { id } => write!(fmt, "{:?}", id.0)?,
        ExprKind::Scope { value, .. } => print_thir_expr(fmt, thir, *value)?,
        _ => write!(fmt, "{:?}", thir[expr_id])?,
    }
    Ok(())
}

/// Term paired with its free variables.
///
/// When we translate contracts, their arguments are not always the same `Ident`s as the arguments
/// of the function they specify. The main culprits are contracts for traits, which are desugared to
/// extra trait methods, with their own `HirId`s, so they are mapped to fresh `Ident`s,
/// and we use the explicit scope to rename them back to the function's `Ident`s.
/// Other contracts are desugared to closures inside the functions they specify, so no renaming is
/// necessary in theory, but the current architecture of Creusot doesn't make this situation easy
/// to untangle.
#[derive(Debug, Clone, TyDecodable, TyEncodable)]
pub struct ScopedTerm<'tcx>(pub Box<[PIdent]>, pub Term<'tcx>);

impl<'tcx> ScopedTerm<'tcx> {
    /// `idents` must be as long as the slice in `self`.
    pub fn rename(&self, idents: &[Ident]) -> Term<'tcx> {
        assert_eq!(idents.len(), self.0.len(), "{:?}.len() != {:?}.len()", idents, self.0);
        let subst: HashMap<_, _> = self
            .0
            .iter()
            .zip(idents)
            .map(|(&from, &to)| (from.0, TermKind::Var(to.into())))
            .collect();
        let mut term = self.1.clone();
        term.subst(&subst);
        term
    }
}
