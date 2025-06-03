// A poorly named module.
//
// Entrypoint for translation of all Pearlite specifications and code: #[logic], contracts, proof_assert!
//
// Transforms THIR into a Term which may be serialized in Creusot metadata files for usage by dependent crates
// The `lower` module then transforms a `Term` into a WhyML expression.

use std::{
    assert_matches::assert_matches,
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
    unreachable,
};

use crate::{
    contracts_items::{
        get_ghost_inner_logic, get_index_logic, is_assertion, is_deref, is_ghost_ty, is_snap_ty,
        is_spec,
    },
    error::{CannotFetchThir, CreusotResult, Error},
    translation::TranslationCtx,
};
use itertools::Itertools;
use log::*;
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
        CanonicalUserType, GenericArg, GenericArgs, GenericArgsRef, Ty, TyCtxt, TyKind,
        TypeFoldable, TypeVisitable, TypeVisitableExt, TypingEnv, UserTypeKind, int_ty, uint_ty,
    },
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{DUMMY_SP, Span};
use rustc_target::abi::{FieldIdx, VariantIdx};
use rustc_type_ir::{FloatTy, IntTy, Interner, UintTy};

mod normalize;

pub(crate) use normalize::*;

#[derive(Copy, Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
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
        typ: DefId,
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
        cur: Box<Term<'tcx>>,
        fin: Box<Term<'tcx>>,
        projection: Projections<Term<'tcx>, Ty<'tcx>>,
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

impl<'tcx> TermKind<'tcx> {
    pub fn item(
        def_id: DefId,
        subst: GenericArgsRef<'tcx>,
        user_ty: &Option<Box<CanonicalUserType<'tcx>>>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        let Some(user_ty) = user_ty else { return Self::Item(def_id, subst) };
        assert!(user_ty.value.bounds.is_empty());
        match user_ty.value.kind {
            UserTypeKind::Ty(_) => Self::Item(def_id, subst),
            UserTypeKind::TypeOf(def_id2, u_subst) => {
                assert_eq!(def_id, def_id2);
                if u_subst.args.len() != subst.len() {
                    return Self::Item(def_id, subst);
                }
                let subst = GenericArgs::for_item(tcx, def_id, |x, _| {
                    let s = subst[x.index as usize];
                    let us = u_subst.args[x.index as usize];
                    if us.has_escaping_bound_vars() { s } else { us }
                });
                Self::Item(def_id, subst)
            }
        }
    }
}

impl<'tcx, I: Interner> TypeFoldable<I> for Literal<'tcx> {
    fn try_fold_with<F: rustc_middle::ty::FallibleTypeFolder<I>>(
        self,
        _: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(self)
    }
}

impl<'tcx, I: Interner> TypeVisitable<I> for Literal<'tcx> {
    fn visit_with<V: rustc_middle::ty::TypeVisitor<I>>(&self, _: &mut V) -> V::Result {
        V::Result::output()
    }
}

pub fn visit_projections<V, T>(v: &Projections<V, T>, mut f: impl FnMut(&V)) {
    v.iter().for_each(|elem| match elem {
        ProjectionElem::Index(v) => f(v),
        _ => {}
    })
}

pub fn visit_projections_mut<V, T>(v: &mut Projections<V, T>, mut f: impl FnMut(&mut V)) {
    v.iter_mut().for_each(|elem| match elem {
        ProjectionElem::Index(v) => f(v),
        _ => {}
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
    Constructor(VariantIdx, Box<[Pattern<'tcx>]>),
    /// Matches the pointed element of a pointer, so for `Box<T>` it matches `T`,
    /// for mutable borrows it matches the *current* value
    Deref(Box<Pattern<'tcx>>),
    Tuple(Box<[Pattern<'tcx>]>),
    Wildcard,
    Binder(PIdent),
    Bool(bool),
}

impl<'tcx> Pattern<'tcx> {
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
        Pattern { ty, kind: PatternKind::Deref(Box::new(self)), span: DUMMY_SP }
    }

    pub(crate) fn constructor(
        variant: VariantIdx,
        fields: impl IntoIterator<Item = Pattern<'tcx>>,
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

    pub(crate) fn rename_binds(&mut self, binders: &mut HashMap<Ident, Ident>) {
        match &mut self.kind {
            PatternKind::Constructor(_, fields) => {
                fields.iter_mut().for_each(|f| f.rename_binds(binders))
            }
            PatternKind::Tuple(fields) => fields.iter_mut().for_each(|f| f.rename_binds(binders)),
            PatternKind::Wildcard => {}
            PatternKind::Binder(s) => {
                let new_ident = s.0.refresh();
                binders.insert(s.0, new_ident);
                s.0 = new_ident;
            }
            PatternKind::Bool(_) => {}
            PatternKind::Deref(pointee) => pointee.rename_binds(binders),
        }
    }

    pub(crate) fn binds(&self, binders: &mut HashSet<Ident>) {
        match &self.kind {
            PatternKind::Constructor(_, fields) => fields.iter().for_each(|f| f.binds(binders)),
            PatternKind::Tuple(fields) => fields.iter().for_each(|f| f.binds(binders)),
            PatternKind::Wildcard => {}
            PatternKind::Binder(s) => {
                binders.insert(s.0);
            }
            PatternKind::Bool(_) => {}
            PatternKind::Deref(pointee) => pointee.binds(binders),
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

pub(crate) fn pearlite_with_triggers<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: LocalDefId,
) -> CreusotResult<(Box<[(PIdent, Ty<'tcx>)]>, Box<[Trigger<'tcx>]>, Term<'tcx>)> {
    let (thir, expr) = ctx.fetch_thir(id)?;
    let thir = thir.borrow();
    if thir.exprs.is_empty() {
        // TODO: why does it not just return `()`?
        return Err(Error::TypeCheck(
            ctx.dcx().span_err(ctx.def_span(id), "Empty body is not allowed").into(),
        ));
    };
    let lower = ThirTerm { ctx, item_id: id, thir: &thir };

    let (triggers, body) = lower.body_term(expr)?;

    // All that remains is to translate patterns in the parameter list.
    // Postconditions make this annoying. They are closures with a `result` parameter,
    // so we have to collect the parameters of the parent function and the current closure.
    let to_pattern =
        |param: &thir::Param<'tcx>| param.pat.as_ref().map(|box pat| lower.pattern_term(pat, true));
    let did = id.into();
    let is_closure = ctx.tcx.is_closure_like(did);
    let patterns: Box<[Pattern]> = if is_spec(ctx.tcx, did) && is_closure {
        // Most specs are closures.
        // Preconditions and variants have all of their variables bound in the parent function.
        // Postconditions also bind a `result` variable.
        let parent = ctx.tcx.parent(did).expect_local();
        let (parent_thir, _) = ctx.fetch_thir(parent)?;
        let parent_thir: &Thir = &parent_thir.borrow();
        // Parameters of the parent function plus maybe the `result` parameter from the current closure
        parent_thir
            .params
            .iter()
            .chain(thir.params.iter().skip(1))
            .filter_map(to_pattern)
            .collect::<CreusotResult<_>>()
    } else if is_closure {
        // Skip implicit `self` parameter.
        thir.params.iter().skip(1).filter_map(to_pattern).collect::<CreusotResult<_>>()
    } else {
        // Case of non-specs or trait item specs (which desugar to extra trait items).
        thir.params.iter().filter_map(to_pattern).collect::<CreusotResult<_>>()
    }?;
    let bound: Box<[(PIdent, Ty<'tcx>)]> = patterns
        .iter()
        .enumerate()
        .map(|(idx, pat)| {
            let ident = match pat.kind {
                PatternKind::Binder(var) => var,
                _ => Ident::fresh_local(&format!("__{}", idx)).into(),
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
impl<'a, 'tcx> ThirTerm<'a, 'tcx> {
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
        match &self.thir[expr].kind {
            ExprKind::Call { ty, args, .. } => {
                if let Some(Stub::Trigger) = pearlite_stub(self.ctx.tcx, *ty) {
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
                if let Block { stmts: box [], expr: Some(expr), .. } = self.thir[*block] {
                    self.collect_triggers(expr, triggers)
                } else {
                    Ok(expr)
                }
            }
            ExprKind::Scope { value, .. } => self.collect_triggers(*value, triggers),
            _ => Ok(expr),
        }
    }

    fn rename(&self, id: HirId) -> PIdent {
        PIdent(self.ctx.rename(id))
    }

    fn expr_term(&self, expr: ExprId) -> CreusotResult<Term<'tcx>> {
        let ty = self.thir[expr].ty;
        let thir_term = &self.thir[expr];
        let span = self.thir[expr].span;
        let res = match thir_term.kind {
            ExprKind::Scope { value, .. } => self.expr_term(value),
            ExprKind::Block { block } => {
                let Block { ref stmts, expr, .. } = self.thir[block];
                let mut inner = match expr {
                    Some(e) => self.expr_term(e)?,
                    None => Term::unit(self.ctx.tcx).span(span),
                };

                for stmt in stmts.iter().rev().filter(|id| not_spec(self.ctx.tcx, self.thir, **id))
                {
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
                    Div => BinOp::Div,
                    Rem => BinOp::Rem,
                    BitXor => BinOp::BitXor,
                    BitAnd => BinOp::BitAnd,
                    BitOr => BinOp::BitOr,
                    Shl | ShlUnchecked => BinOp::Shl,
                    Shr | ShrUnchecked => BinOp::Shr,
                    Lt => BinOp::Lt,
                    Le => BinOp::Le,
                    Ge => BinOp::Ge,
                    Gt => BinOp::Gt,
                    Ne => unreachable!(),
                    Eq => unreachable!(),
                    Offset => todo!(),
                    Cmp => todo!(),
                    AddWithOverflow | SubWithOverflow | MulWithOverflow => todo!(),
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
                    PtrMetadata => todo!(),
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
                                Literal::MachSigned(val, int_ty(ity))
                            }
                            LitIntType::Unsigned(uty) => Literal::MachUnsigned(u, uint_ty(uty)),
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
                    _ => unimplemented!("Unsupported literal"),
                };
                Ok(Term { ty, span, kind: TermKind::Lit(lit) })
            }
            ExprKind::Call { ty: f_ty, ref args, fun, .. } => {
                use Stub::*;
                match pearlite_stub(self.ctx.tcx, f_ty) {
                    Some(s @ (Forall | Exists)) => {
                        let kind =
                            if let Forall = s { QuantKind::Forall } else { QuantKind::Exists };
                        let (binder, trigger, body) = self.quant_term(args[0])?;
                        Ok(body.quant(kind, binder, trigger).span(span))
                    }
                    Some(Fin) => Ok(self.expr_term(args[0])?.fin().span(span)),
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

                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Binary {
                                op: BinOp::Ne,
                                lhs: Box::new(lhs),
                                rhs: Box::new(rhs),
                            },
                        })
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
                            match &self.thir[term].kind {
                                ExprKind::Scope { value, .. } => term = *value,
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
                                        &format!("Bad seq! This should not happen."),
                                    ));
                                }
                            }
                        };
                        Ok(Term { kind: TermKind::SeqLiteral(items), ty, span })
                    }
                    None => {
                        let fun = self.expr_term(fun)?;
                        let (id, subst) = if let TermKind::Item(id, subst) = fun.kind {
                            (id, subst)
                        } else {
                            unreachable!("Call on non-function type");
                        };
                        // HACK: allow dereferencing of `Ghost` in pearlite
                        if let Some(new_subst) = is_ghost_ty_deref(
                            self.ctx.tcx,
                            id,
                            subst.first().and_then(|arg| arg.as_type()),
                        ) {
                            let term = self.expr_term(args[0])?;
                            let inner_id = get_ghost_inner_logic(self.ctx.tcx);
                            Ok(Term {
                                ty,
                                span,
                                kind: TermKind::Call {
                                    id: inner_id,
                                    subst: new_subst,
                                    args: Box::new([term]),
                                },
                            })
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
                            fields.push((
                                missing_field.into(),
                                base.clone().proj(
                                    missing_field.into(),
                                    variant.fields[missing_field.into()].ty(self.ctx.tcx, args),
                                ),
                            ));
                        }
                    }
                    thir::AdtExprBase::DefaultFields(_) => {
                        unimplemented!("default_field_values is not supported in pearlite")
                    }
                }

                fields.sort_by_key(|f| f.0);

                let fields = fields.into_iter().map(|f| f.1).collect();
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Constructor {
                        typ: adt_def.did(),
                        variant: variant_index,
                        fields,
                    },
                })
            }
            ExprKind::Deref { arg } => {
                let arg_trans = self.expr_term(arg)?;
                let arg_ty = self.thir[arg].ty;
                if arg_ty.is_box() || self.thir[arg].ty.ref_mutability() == Some(Not) {
                    Ok(arg_trans.coerce(ty).span(span))
                } else {
                    assert_matches!(arg_ty.kind(), TyKind::Ref(_, _, Mutability::Mut));
                    Ok(arg_trans.cur().span(span))
                }
            }
            ExprKind::Match { scrutinee, ref arms, .. } => {
                let scrutinee = self.expr_term(scrutinee)?;
                if arms.is_empty() {
                    return Err(Error::msg(
                        thir_term.span,
                        "Empty matches are forbidden in Pearlite, because Why3 types are always inhabited.",
                    ));
                }
                let arms = arms.iter().map(|arm| self.arm_term(*arm)).collect::<Result<_, _>>()?;
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Match { scrutinee: Box::new(scrutinee), arms },
                })
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                let cond = self.expr_term(cond)?;
                let then = self.expr_term(then)?;
                let els = if let Some(els) = else_opt {
                    self.expr_term(els)?
                } else {
                    Term::unit(self.ctx.tcx).span(span)
                };
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Match {
                        scrutinee: Box::new(cond),
                        arms: Box::new([
                            (Pattern::bool(self.ctx.tcx, true), then),
                            (Pattern::bool(self.ctx.tcx, false), els),
                        ]),
                    },
                })
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
            // ExprKind::Array { ref fields } => todo!("Array {:?}", fields),
            ExprKind::NonHirLiteral { ref user_ty, .. } => match ty.kind() {
                TyKind::FnDef(id, substs) => {
                    Ok(Term { ty, span, kind: TermKind::item(*id, substs, user_ty, self.ctx.tcx) })
                }
                _ => Err(Error::msg(thir_term.span, "unhandled literal expression")),
            },
            ExprKind::NamedConst { def_id, args, ref user_ty, .. } => {
                Ok(Term { ty, span, kind: TermKind::item(def_id, args, user_ty, self.ctx.tcx) })
            }
            ExprKind::ZstLiteral { ref user_ty, .. } => match ty.kind() {
                TyKind::FnDef(def_id, subst) => Ok(Term {
                    ty,
                    span,
                    kind: TermKind::item(*def_id, subst, user_ty, self.ctx.tcx),
                }),
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
                    thir_term.span,
                    "Casts from ! are not supported in Pearlite, because Why3 types are always inhabited.",
                ))
            }
            ref ek => todo!("lower_expr: {:?}", ek),
        };
        Ok(Term { ty, ..res? })
    }

    fn arm_term(&self, arm: ArmId) -> CreusotResult<(Pattern<'tcx>, Term<'tcx>)> {
        let arm = &self.thir[arm];

        if arm.guard.is_some() {
            return Err(Error::msg(arm.span, "match guards are unsupported"));
        }

        let pattern = self.pattern_term(&arm.pattern, false)?;
        let body = self.expr_term(arm.body)?;

        Ok((pattern, body))
    }

    fn pattern_term(&self, pat: &Pat<'tcx>, mut_allowed: bool) -> CreusotResult<Pattern<'tcx>> {
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
            PatKind::Variant { subpatterns, adt_def, variant_index, args, .. } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, self.pattern_term(&pat.pattern, mut_allowed)?)))
                    .collect::<Result<_, Error>>()?;
                fields.sort_by_key(|f| f.0);

                let defaults = adt_def.variants()[*variant_index]
                    .fields
                    .iter_enumerated()
                    .map(|(idx, f)| (idx, Pattern::wildcard(f.ty(self.ctx.tcx, args))));

                let fields = defaults
                    .merge_join_by(fields, |i: &(FieldIdx, _), j: &(FieldIdx, _)| i.0.cmp(&j.0))
                    .map(|el| el.reduce(|_, a| a).1)
                    .collect();

                Ok(Pattern {
                    ty: pat.ty,
                    span: pat.span,
                    kind: PatternKind::Constructor(*variant_index, fields),
                })
            }
            PatKind::Leaf { subpatterns } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, self.pattern_term(&pat.pattern, mut_allowed)?)))
                    .collect::<Result<_, Error>>()?;
                fields.sort_by_key(|f| f.0);

                if let TyKind::Tuple(_) = pat.ty.kind() {
                    let fields = fields.into_iter().map(|a| a.1).collect();
                    Ok(Pattern { ty: pat.ty, span: pat.span, kind: PatternKind::Tuple(fields) })
                } else {
                    let (adt_def, substs) = if let TyKind::Adt(def, substs) = pat.ty.kind() {
                        (def, substs)
                    } else {
                        unreachable!()
                    };

                    let defaults = adt_def.variants()[0usize.into()]
                        .fields
                        .iter_enumerated()
                        .map(|(idx, f)| (idx, Pattern::wildcard(f.ty(self.ctx.tcx, &substs))));

                    let fields = defaults
                        .merge_join_by(fields, |i: &(FieldIdx, _), j: &(FieldIdx, _)| i.0.cmp(&j.0))
                        .map(|el| el.reduce(|_, a| a).1)
                        .collect();
                    Ok(Pattern {
                        ty: pat.ty,
                        span: pat.span,
                        kind: PatternKind::Constructor(VariantIdx::ZERO, fields),
                    })
                }
            }
            PatKind::Deref { subpattern } => Ok(Pattern {
                ty: pat.ty,
                span: pat.span,
                kind: PatternKind::Deref(Box::new(self.pattern_term(subpattern, mut_allowed)?)),
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
                self.pattern_term(subpattern, mut_allowed)
            }
            ref pk => todo!("lower_pattern: unsupported pattern kind {:?}", pk),
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
                let pattern = self.pattern_term(pattern, false)?;
                if let Some(initializer) = initializer {
                    let initializer = self.expr_term(*initializer)?;
                    let span =
                        init_scope.span(self.ctx.tcx, self.ctx.region_scope_tree(self.item_id));
                    Ok(Term::let_(pattern, initializer, inner).span(span))
                } else {
                    let span = self.ctx.hir().span(HirId {
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
    ) -> Result<(Box<[(PIdent, Ty<'tcx>)]>, Box<[Trigger<'tcx>]>, Term<'tcx>), Error> {
        trace!("{:?}", self.thir[body].kind);
        match self.thir[body].kind {
            ExprKind::Scope { value, .. } => self.quant_term(value),
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                pearlite_with_triggers(self.ctx, closure_id)
            }
            _ => Err(Error::msg(self.thir[body].span, "unexpected error in quantifier")),
        }
    }

    // Creates a 'logical' reborrow of a mutable borrow.
    // The idea is that the expression `&mut ** X` for `X : &mut &mut T` should produces a pearlite value of type `&mut T`.
    //
    // However, this also has to deal with the idea that `* X` access the current value of a borrow in Pearlite.
    // In actuality `&mut ** X` and `*X` are the same thing in THIR (rather the second doesn't exist).
    // This has a **notable** consequence: an hist_inving of a mutable borrow in Pearlite must be the same as its **current value**.
    // That is: `Y = &mut ** X` means that `* Y = ** X` and `^ Y = ^* X`. This is **unlike** in programs in which the `^` and `*` are
    // swapped. While this difference is not satisfactory, it is a natural consequence of the properties of a logic, in particular stability
    //  under substitution. We are allowed to write the following in Pearlite:
    //
    // let a = * x;
    // let b = &mut * a; // &mut cannot be writte in surface syntax.
    //
    // However we translate `&mut x` should be the same as if we had first substituted `a`.
    // This is not fully satisfactory, but the other choice where we correspond to the behavior of programs is not stable under
    // substitution.
    fn logical_reborrow(&self, rebor_id: ExprId) -> Result<TermKind<'tcx>, Error> {
        // Check for the simple `&mut * x` case.
        if let ExprKind::Deref { arg } = self.thir[rebor_id].kind {
            return Ok(self.expr_term(arg)?.kind);
        };
        // eprintln!("{}", PrintExpr(self.thir, rebor_id));
        // Handle every other case.
        let (cur, fin, inner, projection) = self.logical_reborrow_inner(rebor_id)?;

        Ok(TermKind::Reborrow {
            cur: Box::new(cur),
            fin: Box::new(fin),
            inner: Box::new(inner),
            projection: projection.into(),
        })
    }

    fn logical_reborrow_inner(
        &self,
        rebor_id: ExprId,
    ) -> Result<
        (Term<'tcx>, Term<'tcx>, Term<'tcx>, Vec<ProjectionElem<Term<'tcx>, Ty<'tcx>>>),
        Error,
    > {
        let ty = self.thir[rebor_id].ty;
        let span = self.thir[rebor_id].span;
        match &self.thir[rebor_id].kind {
            ExprKind::Scope { value, .. } => self.logical_reborrow_inner(*value),
            ExprKind::Block { block } => {
                let Block { stmts, expr, .. } = &self.thir[*block];
                assert!(stmts.is_empty());
                self.logical_reborrow_inner(expr.unwrap())
            }
            ExprKind::Field { lhs, name, .. } => {
                let (cur, fin, inner, mut proj) = self.logical_reborrow_inner(*lhs)?;
                proj.push(ProjectionElem::Field(*name, ty));
                Ok((cur.proj(*name, ty).span(span), fin.proj(*name, ty).span(span), inner, proj))
            }
            ExprKind::Deref { arg } => {
                // Detect * snapshot_deref & and treat that as a single 'projection'
                if self.is_snapshot_deref(*arg) {
                    let ExprKind::Call { args, .. } = &self.thir[*arg].kind else { unreachable!() };
                    let ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } =
                        self.thir[args[0]].kind
                    else {
                        unreachable!()
                    };

                    let (cur, fin, inner, proj) = self.logical_reborrow_inner(arg)?;
                    // Extract the `T` from `Snapshot<T>`
                    let TyKind::Adt(_, subst) = self.thir[arg].ty.peel_refs().kind() else {
                        unreachable!()
                    };
                    let ty = subst.type_at(0);
                    return Ok((
                        Term { ty, kind: TermKind::Coerce { arg: Box::new(cur) }, span },
                        Term { ty, kind: TermKind::Coerce { arg: Box::new(fin) }, span },
                        inner,
                        proj,
                    ));
                };

                match self.thir[*arg].ty.kind() {
                    TyKind::Ref(_, _, Mutability::Mut) => {
                        let inner = self.expr_term(*arg)?;
                        Ok((
                            inner.clone().cur().span(span),
                            inner.clone().fin().span(span),
                            inner.span(span),
                            Vec::new(),
                        ))
                    }
                    TyKind::Adt(adtdef, _) if adtdef.is_box() => {
                        let mut res = self.logical_reborrow_inner(*arg)?;
                        res.3.push(ProjectionElem::Deref);
                        Ok(res)
                    }
                    _ => unreachable!("Unexpected deref type: {ty:?}."),
                }
            }
            e @ ExprKind::Call { ty: fn_ty, args, .. } if fn_ty.is_fn() => {
                let index_logic_method = get_index_logic(self.ctx.tcx);

                let TyKind::FnDef(id, _) = fn_ty.kind() else { panic!("expected function type") };

                let (cur, fin, inner, mut proj) = self.logical_reborrow_inner(args[0])?;

                if !matches!(
                    self.thir[args[0]].ty.kind(),
                    TyKind::Str | TyKind::Array(_, _) | TyKind::Slice(_)
                ) {
                    return Err(Error::msg(
                        span,
                        format!(
                            "unsupported logical reborrow of indexing {e:?}, only slice indexing is supported"
                        ),
                    ));
                }

                if id == &index_logic_method {
                    let index = self.expr_term(args[1])?;
                    proj.push(ProjectionElem::Index(index.clone()));

                    let subst =
                        self.ctx.mk_args(&[GenericArg::from(cur.ty), GenericArg::from(index.ty)]);

                    Ok((
                        Term::call_no_normalize(self.ctx.tcx, index_logic_method, subst, [
                            cur,
                            index.clone(),
                        ]),
                        Term::call_no_normalize(self.ctx.tcx, index_logic_method, subst, [
                            fin, index,
                        ]),
                        inner,
                        proj,
                    ))
                } else {
                    Err(Error::msg(span, format!("unsupported projection {id:?}")))
                }
            }
            e => Err(Error::msg(
                span,
                format!(
                    "unsupported logical reborrow {e:?}, only field projections and slice indexing are supported"
                ),
            )),
        }
    }

    pub(crate) fn is_snapshot_deref(&self, expr_id: ExprId) -> bool {
        let ExprKind::Call { ty, .. } = &self.thir[expr_id].kind else { return false };
        let TyKind::FnDef(id, sub) = ty.kind() else { panic!("expected function type") };
        is_deref(self.ctx.tcx, *id)
            && sub.type_at(0).ty_adt_def().is_some_and(|d| is_snap_ty(self.ctx.tcx, d.did()))
    }
}

fn is_ghost_ty_deref<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_id: DefId,
    ty: Option<Ty<'tcx>>,
) -> Option<&'tcx GenericArgs<'tcx>> {
    let ty = ty?;
    if !is_deref(tcx, fn_id) {
        return None;
    }
    match ty.kind() {
        rustc_type_ir::TyKind::Adt(containing_type, new_subst) => {
            if is_ghost_ty(tcx, containing_type.did()) { Some(new_subst) } else { None }
        }
        _ => None,
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
    Fin,
    Impl,
    Equals,
    Neq,
    VariantCheck,
    Old,
    ResultCheck,
    Dead,
    SeqLiteral,
}

pub(crate) fn pearlite_stub<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Stub> {
    if let TyKind::FnDef(id, _) = *ty.kind() {
        match tcx.get_diagnostic_name(id)?.as_str() {
            "forall" => Some(Stub::Forall),
            "exists" => Some(Stub::Exists),
            "trigger" => Some(Stub::Trigger),
            "fin" => Some(Stub::Fin),
            "implication" => Some(Stub::Impl),
            "equal" => Some(Stub::Equals),
            "neq" => Some(Stub::Neq),
            "variant_check" => Some(Stub::VariantCheck),
            "old" => Some(Stub::Old),
            "dead" => Some(Stub::Dead),
            "closure_result_constraint" => Some(Stub::ResultCheck),
            "seq_literal" => Some(Stub::SeqLiteral),
            _ => None,
        }
    } else {
        None
    }
}

fn not_spec(tcx: TyCtxt<'_>, thir: &Thir<'_>, id: StmtId) -> bool {
    match thir[id].kind {
        StmtKind::Expr { expr, .. } => not_spec_expr(tcx, thir, expr),
        StmtKind::Let { initializer, .. } => {
            if let Some(initializer) = initializer {
                not_spec_expr(tcx, thir, initializer)
            } else {
                true
            }
        }
    }
}

fn not_spec_expr(tcx: TyCtxt<'_>, thir: &Thir<'_>, id: ExprId) -> bool {
    match thir[id].kind {
        ExprKind::Scope { value, .. } => not_spec_expr(tcx, thir, value),
        ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
            !is_spec(tcx, closure_id.to_def_id())
        }
        _ => true,
    }
}

pub trait TermVisitor<'tcx> {
    fn visit_term(&mut self, term: &Term<'tcx>);
}

pub fn super_visit_term<'tcx, V: TermVisitor<'tcx>>(term: &Term<'tcx>, visitor: &mut V) {
    match &term.kind {
        TermKind::Var(_) => {}
        TermKind::Lit(_) => {}
        TermKind::SeqLiteral(fields) => fields.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Cast { arg } => visitor.visit_term(arg),
        TermKind::Coerce { arg } => visitor.visit_term(arg),
        TermKind::Item(_, _) => {}
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
        TermKind::Constructor { typ: _, variant: _, fields } => {
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
            arms.iter().for_each(|(_, arm)| visitor.visit_term(arm))
        }
        TermKind::Let { pattern: _, arg, body } => {
            visitor.visit_term(arg);
            visitor.visit_term(body)
        }
        TermKind::Projection { lhs, idx: _ } => visitor.visit_term(lhs),
        TermKind::Old { term } => visitor.visit_term(term),
        TermKind::Closure { body, .. } => visitor.visit_term(body),
        TermKind::Reborrow { cur, fin, inner, projection } => {
            visitor.visit_term(cur);
            visitor.visit_term(fin);
            visitor.visit_term(inner);
            visit_projections(projection, |term| visitor.visit_term(term))
        }
        TermKind::Assert { cond } => visitor.visit_term(cond),
        TermKind::Precondition { params, .. } => params.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Postcondition { params, .. } => params.iter().for_each(|a| visitor.visit_term(a)),
    }
}

pub trait TermVisitorMut<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>);
}

pub(crate) fn super_visit_mut_term<'tcx, V: TermVisitorMut<'tcx>>(
    term: &mut Term<'tcx>,
    visitor: &mut V,
) {
    match &mut term.kind {
        TermKind::Var(_) => {}
        TermKind::Lit(_) => {}
        TermKind::SeqLiteral(fields) => fields.iter_mut().for_each(|a| visitor.visit_mut_term(a)),
        TermKind::Cast { arg } => visitor.visit_mut_term(&mut *arg),
        TermKind::Coerce { arg } => visitor.visit_mut_term(arg),
        TermKind::Item(_, _) => {}
        TermKind::Binary { op: _, lhs, rhs } => {
            visitor.visit_mut_term(&mut *lhs);
            visitor.visit_mut_term(&mut *rhs);
        }
        TermKind::Unary { op: _, arg } => visitor.visit_mut_term(&mut *arg),
        TermKind::Quant { body, trigger, .. } => {
            trigger.iter_mut().flat_map(|x| &mut x.0).for_each(|x| visitor.visit_mut_term(x));
            visitor.visit_mut_term(&mut *body)
        }
        TermKind::Call { id: _, subst: _, args } => {
            args.iter_mut().for_each(|a| visitor.visit_mut_term(&mut *a))
        }
        TermKind::Constructor { typ: _, variant: _, fields } => {
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
            arms.iter_mut().for_each(|(_, arm)| visitor.visit_mut_term(&mut *arm))
        }
        TermKind::Let { pattern: _, arg, body } => {
            visitor.visit_mut_term(&mut *arg);
            visitor.visit_mut_term(&mut *body)
        }
        TermKind::Projection { lhs, idx: _ } => visitor.visit_mut_term(&mut *lhs),
        TermKind::Old { term } => visitor.visit_mut_term(&mut *term),
        TermKind::Closure { body, .. } => visitor.visit_mut_term(&mut *body),
        TermKind::Reborrow { cur, fin, inner, projection } => {
            visitor.visit_mut_term(&mut *cur);
            visitor.visit_mut_term(&mut *fin);
            visitor.visit_mut_term(&mut *inner);
            visit_projections_mut(projection, |term| visitor.visit_mut_term(term))
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
            span: DUMMY_SP,
            ty: body.ty,
            kind: TermKind::Let { pattern, arg: Box::new(arg), body: Box::new(body) },
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
        Term { ty, kind: TermKind::Projection { lhs: Box::new(self), idx }, span: DUMMY_SP }
    }

    pub(crate) fn tuple(tcx: TyCtxt<'tcx>, fields: impl IntoIterator<Item = Term<'tcx>>) -> Self {
        let fields: Box<[_]> = fields.into_iter().collect();
        let ty = Ty::new_tup_from_iter(tcx, fields.iter().map(|t| t.ty));
        Term { ty, kind: TermKind::Tuple { fields }, span: DUMMY_SP }
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
                    kind: TermKind::Binary {
                        op: BinOp::And,
                        lhs: Box::new(self),
                        rhs: Box::new(rhs),
                    },
                    span: DUMMY_SP,
                },
            },
        }
    }

    pub(crate) fn bin_op(self, ty: Ty<'tcx>, op: BinOp, rhs: Self) -> Self {
        Term {
            ty,
            kind: TermKind::Binary { op, lhs: Box::new(self), rhs: Box::new(rhs) },
            span: DUMMY_SP,
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
                kind: TermKind::Impl { lhs: Box::new(self), rhs: Box::new(rhs) },
                span: DUMMY_SP,
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
                kind: TermKind::Quant { kind: quant_kind, binder, body: Box::new(self), trigger },
                span: DUMMY_SP,
            },
        }
    }

    pub(crate) fn coerce(self, ty: Ty<'tcx>) -> Self {
        Term { ty, kind: TermKind::Coerce { arg: Box::new(self) }, span: DUMMY_SP }
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
    /// - If `self` is `forall<x: Int> x == 1`, `self.subst(inv_subst)` is still `forall<x: Int> x == 1`
    pub(crate) fn subst(&mut self, subst: impl IntoSubst<'tcx>) {
        self.subst_with(&HashMap::new(), &mut subst.into_subst())
    }

    fn subst_with<F: FnMut(Ident) -> Option<TermKind<'tcx>>>(
        &mut self,
        bound: &HashMap<Ident, Ident>,
        subst: &mut F,
    ) {
        match &mut self.kind {
            TermKind::Var(v) => match bound.get(&v.0) {
                Some(w) => v.0 = *w,
                None if let Some(t) = subst(v.0) => self.kind = t,
                None => {}
            },
            TermKind::Lit(_) => {}
            TermKind::SeqLiteral(fields) => {
                fields.iter_mut().for_each(|a| a.subst_with(bound, subst))
            }
            TermKind::Cast { arg } => arg.subst_with(bound, subst),
            TermKind::Coerce { arg } => arg.subst_with(bound, subst),
            TermKind::Item(_, _) => {}
            TermKind::Binary { lhs, rhs, .. } => {
                lhs.subst_with(bound, subst);
                rhs.subst_with(bound, subst)
            }
            TermKind::Unary { arg, .. } => arg.subst_with(bound, subst),
            TermKind::Quant { binder, trigger, body, kind: _ } => {
                let mut bound = bound.clone();
                for (ident, _) in binder {
                    let new_ident = ident.0.refresh();
                    bound.insert(ident.0, new_ident);
                    ident.0 = new_ident;
                }
                trigger
                    .iter_mut()
                    .flat_map(|ts| &mut ts.0)
                    .for_each(|t| t.subst_with(&bound, subst));
                body.subst_with(&bound, subst);
            }
            TermKind::Call { args, .. } => args.iter_mut().for_each(|f| f.subst_with(bound, subst)),
            TermKind::Constructor { fields, .. } => {
                fields.iter_mut().for_each(|f| f.subst_with(bound, subst))
            }
            TermKind::Tuple { fields } => {
                fields.iter_mut().for_each(|f| f.subst_with(bound, subst))
            }
            TermKind::Cur { term } => term.subst_with(bound, subst),
            TermKind::Fin { term } => term.subst_with(bound, subst),
            TermKind::Impl { lhs, rhs } => {
                lhs.subst_with(bound, subst);
                rhs.subst_with(bound, subst)
            }
            TermKind::Match { scrutinee, arms } => {
                scrutinee.subst_with(bound, subst);
                arms.iter_mut().for_each(|(pat, arm)| {
                    let mut bound = bound.clone();
                    pat.rename_binds(&mut bound);
                    arm.subst_with(&bound, subst);
                })
            }
            TermKind::Let { pattern, arg, body } => {
                arg.subst_with(bound, subst);
                let mut bound = bound.clone();
                pattern.rename_binds(&mut bound);
                body.subst_with(&bound, subst);
            }
            TermKind::Projection { lhs, .. } => lhs.subst_with(bound, subst),
            TermKind::Old { term } => term.subst_with(bound, subst),
            TermKind::Closure { body, bound: bound_new } => {
                let mut bound = bound.clone();
                bound.extend(bound_new.iter_mut().map(|(ident, _)| {
                    let rnm = (ident.0, ident.0.refresh());
                    ident.0 = rnm.1;
                    rnm
                }));
                body.subst_with(&bound, subst);
            }
            TermKind::Reborrow { cur, fin, inner, projection } => {
                cur.subst_with(bound, subst);
                fin.subst_with(bound, subst);
                inner.subst_with(bound, subst);
                visit_projections_mut(projection, |term| term.subst_with(bound, subst))
            }
            TermKind::Assert { cond } => cond.subst_with(bound, subst),
            TermKind::Precondition { params, .. } => {
                params.iter_mut().for_each(|p| p.subst_with(bound, subst))
            }
            TermKind::Postcondition { params, .. } => {
                params.iter_mut().for_each(|p| p.subst_with(bound, subst))
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
            TermKind::Item(_, _) => {}
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
            TermKind::Reborrow { cur, fin, inner, projection } => {
                cur.free_vars_inner(bound, free);
                fin.free_vars_inner(bound, free);
                inner.free_vars_inner(bound, free);
                visit_projections(projection, |term| term.free_vars_inner(bound, free))
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

pub(crate) trait IntoSubst<'tcx> {
    fn into_subst(self) -> impl Fn(Ident) -> Option<TermKind<'tcx>>;
}

/// A substitution from a mapping of `Ident` to `TermKind`.
pub type MapSubstitution<'tcx> = HashMap<Ident, TermKind<'tcx>>;

impl<'tcx> IntoSubst<'tcx> for &MapSubstitution<'tcx> {
    fn into_subst(self) -> impl Fn(Ident) -> Option<TermKind<'tcx>> {
        move |k| self.get(&k).cloned()
    }
}

/// A renaming from `Ident` to `Ident` in a small array.
pub struct SmallRenaming<const N: usize>(pub [(Ident, Ident); N]);

impl<'tcx, const N: usize> IntoSubst<'tcx> for &SmallRenaming<N> {
    fn into_subst(self) -> impl Fn(Ident) -> Option<TermKind<'tcx>> {
        move |x| {
            for &(from, to) in &self.0 {
                if from == x {
                    return Some(TermKind::Var(to.into()));
                }
            }
            None
        }
    }
}

impl<'tcx, F: Fn(Ident) -> Option<TermKind<'tcx>>> IntoSubst<'tcx> for F {
    fn into_subst(self) -> impl Fn(Ident) -> Option<TermKind<'tcx>> {
        self
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
        ExprKind::VarRef { id } => {
            write!(fmt, "{:?}", id.0)?;
        }
        ExprKind::Scope { value, .. } => {
            print_thir_expr(fmt, thir, *value)?;
        }
        _ => {
            write!(fmt, "{:?}", thir[expr_id])?;
        }
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
