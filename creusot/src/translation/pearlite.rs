use crate::translation::pearlite::visit::{visit_projections, visit_projections_mut};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::{Mutability, visit::VisitorResult};
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{BorrowKind, Mutability::*, ProjectionElem},
    thir::{ExprId, ExprKind, Thir},
    ty::{
        Const, GenericArgsRef, ParamConst, Ty, TyCtxt, TyKind, TypeFoldable, TypeVisitable,
        TypingEnv,
    },
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{DUMMY_SP, Span};
use rustc_type_ir::{FloatTy, IntTy, Interner, UintTy};
use std::{
    assert_matches::assert_matches,
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
};

mod from_thir;
mod normalize;
pub mod visit;

pub(crate) use from_thir::from_thir;
pub(crate) use normalize::normalize;

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
    Capture(FieldIdx),
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
            TermKind::Lit(_) | TermKind::Capture(_) => {}
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
            TermKind::Lit(_) | TermKind::Capture(_) => {}
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
