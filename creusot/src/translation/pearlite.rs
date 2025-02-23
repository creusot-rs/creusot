// A poorly named module.
//
// Entrypoint for translation of all Pearlite specifications and code: #[logic], contracts, proof_assert!
//
// Transforms THIR into a Term which may be serialized in Creusot metadata files for usage by dependent crates
// The `lower` module then transforms a `Term` into a WhyML expression.

use std::{
    collections::HashSet,
    fmt::{Display, Formatter},
    unreachable,
};

use crate::{
    contracts_items::{
        get_ghost_inner_logic, get_index_logic, is_assertion, is_deref, is_ghost_ty, is_snap_ty,
        is_spec,
    },
    error::{CannotFetchThir, CreusotResult, Error},
    naming::anonymous_param_symbol,
    translation::TranslationCtx,
};
use itertools::Itertools;
use log::*;
use rustc_ast::{visit::VisitorResult, ByRef, LitIntType, LitKind, Mutability};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    HirId, OwnerId,
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
pub(crate) use rustc_middle::thir;
use rustc_middle::{
    mir::{BorrowKind, Mutability::*, ProjectionElem},
    thir::{
        AdtExpr, ArmId, Block, ClosureExpr, ExprId, ExprKind, Pat, PatKind, StmtId, StmtKind, Thir,
    },
    ty::{
        int_ty, uint_ty, CanonicalUserType, GenericArg, GenericArgs, GenericArgsRef, Ty, TyCtxt,
        TyKind, TypeFoldable, TypeVisitable, TypeVisitableExt, TypingEnv, UserTypeKind,
    },
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{symbol::Ident, Span, Symbol, DUMMY_SP};
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

pub type QuantBinder<'tcx> = (Box<[Ident]>, Ty<'tcx>);

pub type Projections<V, T> = Box<[ProjectionElem<V, T>]>;

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum TermKind<'tcx> {
    Var(Symbol),
    Lit(Literal<'tcx>),
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
        name: FieldIdx,
    },
    Old {
        term: Box<Term<'tcx>>,
    },
    Closure {
        bound: Box<[Symbol]>,
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
        args: GenericArgsRef<'tcx>,
        params: Box<[Term<'tcx>]>,
    },
    /// Inferred postconditions for `(item, args)`
    Postcondition {
        item: DefId,
        args: GenericArgsRef<'tcx>,
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
                    if us.has_escaping_bound_vars() {
                        s
                    } else {
                        us
                    }
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
pub enum Pattern<'tcx> {
    Constructor {
        variant: DefId,
        substs: GenericArgsRef<'tcx>,
        fields: Box<[Pattern<'tcx>]>,
    },
    /// Matches the pointed element of a pointer, so for `Box<T>` it matches `T`, for mutable borrows it matches the *current* value
    Deref {
        pointee: Box<Pattern<'tcx>>,
        kind: PointerKind,
    },
    Tuple(Box<[Pattern<'tcx>]>),
    Wildcard,
    Binder(Symbol),
    Boolean(bool),
}

// TODO: Pattern should store a type directly
#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum PointerKind {
    Box,
    Shr,
    Mut,
}

const TRIGGER_ERROR: &str = "Triggers can only be used inside quantifiers";
pub(crate) fn pearlite<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: LocalDefId,
) -> CreusotResult<Term<'tcx>> {
    let (triggers, term) = pearlite_with_triggers(ctx, id)?;
    if !triggers.is_empty() {
        Err(Error::msg(ctx.def_span(id), TRIGGER_ERROR))
    } else {
        Ok(term)
    }
}

pub(crate) fn pearlite_with_triggers<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: LocalDefId,
) -> CreusotResult<(Box<[Trigger<'tcx>]>, Term<'tcx>)> {
    let (thir, expr) = ctx.fetch_thir(id)?;
    let thir = thir.borrow();
    if thir.exprs.is_empty() {
        return Err(Error::TypeCheck(CannotFetchThir));
    };

    let lower = ThirTerm { ctx, item_id: id, thir: &thir };

    lower.body_term(expr)
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

        let did = self.item_id.into();
        let owner_id = if is_spec(self.ctx.tcx, did) && self.ctx.tcx.is_closure_like(did) {
            self.ctx.tcx.parent(did).expect_local()
        } else {
            self.item_id
        };

        let (thir, _) = self.ctx.fetch_thir(owner_id)?;
        let thir: &Thir = &thir.borrow();
        let res = thir
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                Some(Self::pattern_term(param.pat.as_ref()?, true).map(|pat| (idx, param.ty, pat)))
            })
            .fold_ok(body, |body, (idx, ty, pattern)| match pattern {
                Pattern::Binder(_) | Pattern::Wildcard => body,
                _ => {
                    let arg = Box::new(Term::var(anonymous_param_symbol(idx), ty));
                    Term {
                        ty: body.ty,
                        span: body.span,
                        kind: TermKind::Let { pattern, arg, body: Box::new(body) },
                    }
                }
            })?;
        Ok((triggers.into(), res))
    }

    fn collect_triggers(
        &self,
        expr: ExprId,
        triggers: &mut Vec<Trigger<'tcx>>,
    ) -> CreusotResult<ExprId> {
        match &self.thir[expr].kind {
            ExprKind::Call { ty: f_ty, ref args, .. } => {
                if let Some(Stub::Trigger) = pearlite_stub(self.ctx.tcx, *f_ty) {
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
                    None => Term { ty, span, kind: TermKind::Tuple { fields: Box::new([]) } },
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
            ExprKind::VarRef { id } => {
                let map = self.ctx.hir();
                let name = map.name(id.0);
                Ok(Term { ty, span, kind: TermKind::Var(name) })
            }
            // TODO: confirm this works
            ExprKind::UpvarRef { var_hir_id: id, .. } => {
                let map = self.ctx.hir();
                let name = map.name(id.0);

                Ok(Term { ty, span, kind: TermKind::Var(name) })
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
                        let (binder, (trigger, body)) = self.quant_term(args[0])?;
                        let arg_tuple_ty = if let TyKind::FnDef(_, subst) = f_ty.kind() {
                            subst[0].as_type().unwrap()
                        } else {
                            unreachable!()
                        };
                        let binder = (binder, arg_tuple_ty);

                        Ok(body.quant(kind, binder, trigger).span(span))
                    }
                    Some(Fin) => {
                        let term = self.expr_term(args[0])?;

                        Ok(Term { ty, span, kind: TermKind::Fin { term: Box::new(term) } })
                    }
                    Some(Impl) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;

                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Impl { lhs: Box::new(lhs), rhs: Box::new(rhs) },
                        })
                    }
                    Some(Equals) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;

                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Binary {
                                op: BinOp::Eq,
                                lhs: Box::new(lhs),
                                rhs: Box::new(rhs),
                            },
                        })
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
                    Some(ResultCheck) => {
                        Ok(Term { ty, span, kind: TermKind::Tuple { fields: Box::new([]) } })
                    }
                    Some(Dead) => Err(Error::msg(
                        span,
                        "The `dead` term can only be used for the body of trusted logical functions",
                    )),
                    Some(Trigger) => Err(Error::msg(
                        span,
                        "Triggers can only be used directly inside quantifiers",
                    )),
                    None => {
                        let fun = self.expr_term(fun)?;
                        let (id, subst) = if let TermKind::Item(id, subst) = fun.kind {
                            (id, subst)
                        } else {
                            unreachable!("Call on non-function type");
                        };
                        // HACK: allow dereferencing of GhostBox in pearlite
                        if let Some(new_subst) = is_ghost_box_deref(
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
                            let args = args
                                .iter()
                                .map(|arg| self.expr_term(*arg))
                                .collect::<Result<_, _>>()?;

                            Ok(Term { ty, span, kind: TermKind::Call { id, subst, args } })
                        }
                    }
                }
            }
            ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } => Ok({
                Term { ty, kind: TermKind::Coerce { arg: Box::new(self.expr_term(arg)?) }, span }
            }),
            ExprKind::Borrow { arg, .. } => {
                let t = self.logical_reborrow(arg)?;
                Ok(Term { ty, span, kind: t })
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
                                Term {
                                    ty: variant.fields[missing_field.into()].ty(self.ctx.tcx, args),
                                    span: DUMMY_SP,
                                    kind: mk_projection(base.clone(), missing_field.into()),
                                },
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
                if self.thir[arg].ty.is_box() || self.thir[arg].ty.ref_mutability() == Some(Not) {
                    let ty = arg_trans.ty.builtin_deref(false).expect("expected &T or Box<T>");
                    Ok(Term { ty, kind: TermKind::Coerce { arg: Box::new(arg_trans) }, span })
                } else {
                    Ok(Term { ty, span, kind: TermKind::Cur { term: Box::new(arg_trans) } })
                }
            }
            ExprKind::Match { scrutinee, ref arms, .. } => {
                let scrutinee = self.expr_term(scrutinee)?;
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
                    Term {
                        span,
                        ty: self.ctx.types.unit,
                        kind: TermKind::Tuple { fields: Box::new([]) },
                    }
                };
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Match {
                        scrutinee: Box::new(cond),
                        arms: Box::new([
                            (Pattern::Boolean(true), then),
                            (Pattern::Boolean(false), els),
                        ]),
                    },
                })
            }
            ExprKind::Field { lhs, name, .. } => {
                let lhs = self.expr_term(lhs)?;
                Ok(Term { ty, span, kind: mk_projection(lhs, name) })
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
                let term = pearlite(self.ctx, closure_id)?;

                if is_assertion(self.ctx.tcx, closure_id.to_def_id()) {
                    Ok(Term { ty, span, kind: TermKind::Assert { cond: Box::new(term) } })
                } else {
                    let bound = self.ctx.fn_arg_names(closure_id).iter().map(|i| i.name).collect();
                    Ok(Term { ty, span, kind: TermKind::Closure { bound, body: Box::new(term) } })
                }
            }
            ExprKind::Cast { source } => {
                let source = self.expr_term(source)?;
                Ok(Term { ty, span, kind: TermKind::Cast { arg: Box::new(source) } })
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

        let pattern = Self::pattern_term(&arm.pattern, false)?;
        let body = self.expr_term(arm.body)?;

        Ok((pattern, body))
    }

    fn pattern_term(pat: &Pat<'tcx>, mut_allowed: bool) -> CreusotResult<Pattern<'tcx>> {
        trace!("{:?}", pat);
        match &pat.kind {
            PatKind::Wild => Ok(Pattern::Wildcard),
            PatKind::Binding { name, mode, .. } => {
                if mode.0 == ByRef::Yes(Mutability::Mut) {
                    return Err(Error::msg(
                        pat.span,
                        "mut ref binders are not supported in pearlite",
                    ));
                }
                if !mut_allowed && mode.1 == Mutability::Mut {
                    return Err(Error::msg(pat.span, "mut binders are not supported in pearlite"));
                }
                Ok(Pattern::Binder(*name))
            }
            PatKind::Variant { subpatterns, adt_def, variant_index, args, .. } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, Self::pattern_term(&pat.pattern, mut_allowed)?)))
                    .collect::<Result<_, Error>>()?;
                fields.sort_by_key(|f| f.0);

                let field_count = adt_def.variants()[*variant_index].fields.len();
                let defaults = (0usize..field_count).map(|i| (i.into(), Pattern::Wildcard));

                let fields = defaults
                    .merge_join_by(fields, |i: &(FieldIdx, _), j: &(FieldIdx, _)| i.0.cmp(&j.0))
                    .map(|el| el.reduce(|_, a| a).1)
                    .collect();

                Ok(Pattern::Constructor {
                    variant: adt_def.variants()[*variant_index].def_id,
                    substs: args,
                    fields,
                })
            }
            PatKind::Leaf { subpatterns } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, Self::pattern_term(&pat.pattern, mut_allowed)?)))
                    .collect::<Result<_, Error>>()?;
                fields.sort_by_key(|f| f.0);

                if matches!(pat.ty.kind(), TyKind::Tuple(_)) {
                    let fields = fields.into_iter().map(|a| a.1).collect();
                    Ok(Pattern::Tuple(fields))
                } else {
                    let (adt_def, substs) = if let TyKind::Adt(def, substs) = pat.ty.kind() {
                        (def, substs)
                    } else {
                        unreachable!()
                    };

                    let field_count = adt_def.variants()[0usize.into()].fields.len();
                    let defaults = (0..field_count).map(|i| (i.into(), Pattern::Wildcard));

                    let fields = defaults
                        .merge_join_by(fields, |i: &(FieldIdx, _), j: &(FieldIdx, _)| i.0.cmp(&j.0))
                        .map(|el| el.reduce(|_, a| a).1)
                        .collect();
                    Ok(Pattern::Constructor {
                        variant: adt_def.variants()[0usize.into()].def_id,
                        substs,
                        fields,
                    })
                }
            }
            PatKind::Deref { subpattern } => {
                if !(pat.ty.is_box() || pat.ty.ref_mutability() == Some(Not)) {
                    return Err(Error::msg(
                        pat.span,
                        "only deref patterns for box and & are supported",
                    ));
                }

                Self::pattern_term(subpattern, mut_allowed)
            }
            PatKind::Constant { value } => {
                if !pat.ty.is_bool() {
                    return Err(Error::msg(
                        pat.span,
                        "non-boolean constant patterns are unsupported",
                    ));
                }
                Ok(Pattern::Boolean(value.try_to_bool().unwrap()))
            }
            // TODO: this simply ignores type annotations, maybe we should actually support them
            PatKind::AscribeUserType { ascription: _, subpattern } => {
                Self::pattern_term(subpattern, mut_allowed)
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

                Ok(Term {
                    ty: inner.ty,
                    span,
                    kind: TermKind::Let {
                        pattern: Pattern::Wildcard,
                        arg: Box::new(arg),
                        body: Box::new(inner),
                    },
                })
            }
            StmtKind::Let { pattern, initializer, init_scope, .. } => {
                let pattern = Self::pattern_term(pattern, false)?;
                if let Some(initializer) = initializer {
                    let initializer = self.expr_term(*initializer)?;
                    let span =
                        init_scope.span(self.ctx.tcx, self.ctx.region_scope_tree(self.item_id));
                    Ok(Term {
                        ty: inner.ty,
                        span,
                        kind: TermKind::Let {
                            pattern,
                            arg: Box::new(initializer),
                            body: Box::new(inner),
                        },
                    })
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
    ) -> Result<(Box<[Ident]>, (Box<[Trigger<'tcx>]>, Term<'tcx>)), Error> {
        trace!("{:?}", self.thir[body].kind);
        match self.thir[body].kind {
            ExprKind::Scope { value, .. } => self.quant_term(value),
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                let names = self.ctx.fn_arg_names(closure_id);

                Ok((names.into(), pearlite_with_triggers(self.ctx, closure_id)?))
            }
            _ => Err(Error::msg(self.thir[body].span, "unexpected error in quantifier")),
        }
    }

    // Creates a 'logical' reborrow of a mutable borrow.
    // The idea is that the expression `&mut ** X` for `X : &mut &mut T` should produces a pearlite value of type `&mut T`.
    //
    // However, this also has to deal with the idea that `* X` access the current value of a borrow in Pearlite.
    // In actuality `&mut ** X` and `*X` are the same thing in THIR (rather the second doesn't exist).
    // This has a **notable** consequence: an unnesting of a mutable borrow in Pearlite must be the same as its **current value**.
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
            ExprKind::Field { lhs, variant_index: _, name } => {
                let (cur, fin, inner, mut proj) = self.logical_reborrow_inner(*lhs)?;
                proj.push(ProjectionElem::Field(*name, ty));
                Ok((
                    Term { ty, span, kind: mk_projection(cur, *name) },
                    Term { ty, span, kind: mk_projection(fin, *name) },
                    inner,
                    proj
                ))
            }
            ExprKind::Deref { arg } => {
                // Detect * snapshot_deref & and treat that as a single 'projection'
                if self.is_snapshot_deref(*arg) {
                    let ExprKind::Call { args, .. } = &self.thir[*arg].kind else { unreachable!() };
                    let ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } = self.thir[args[0]].kind else { unreachable!() };

                    let (cur, fin, inner, proj) = self.logical_reborrow_inner(arg)?;
                    // Extract the `T` from `Snapshot<T>`
                    let TyKind::Adt(_, subst) = self.thir[arg].ty.peel_refs().kind() else { unreachable!() };
                    let ty = subst.type_at(0);
                    return Ok((
                        Term { ty, kind: TermKind::Coerce { arg: Box::new(cur) }, span },
                        Term { ty, kind: TermKind::Coerce { arg: Box::new(fin) }, span },
                        inner,
                        proj
                    ));
                };

                match self.thir[*arg].ty.kind() {
                    TyKind::Ref(_, _, Mutability::Mut) => {
                        let inner = self.expr_term(*arg)?;
                        Ok((inner.clone().cur().span(span), inner.clone().fin().span(span), inner.span(span), Vec::new()))
                    }
                    TyKind::Adt(adtdef, _) if adtdef.is_box() => {
                        let mut res = self.logical_reborrow_inner(*arg)?;
                        res.3.push(ProjectionElem::Deref);
                        Ok(res)
                    }
                    _ => unreachable!("Unexpected deref type: {ty:?}.")
                }
            }
            e @ ExprKind::Call { ty: fn_ty, args, .. } if fn_ty.is_fn() => {
                let index_logic_method = get_index_logic(self.ctx.tcx);

                let TyKind::FnDef(id,_) = fn_ty.kind() else { panic!("expected function type") };

                let (cur, fin, inner, mut proj) = self.logical_reborrow_inner(args[0])?;

                if !matches!(self.thir[args[0]].ty.kind(), TyKind::Str | TyKind::Array(_, _) | TyKind::Slice(_)) {
                    return Err(Error::msg(
                        span,
                        format!("unsupported logical reborrow of indexing {e:?}, only slice indexing is supported"),
                    ))
                }

                if id == &index_logic_method {
                    let index = self.expr_term(args[1])?;
                    proj.push(ProjectionElem::Index(index.clone()));

                    let subst =
                        self.ctx.mk_args(&[GenericArg::from(cur.ty), GenericArg::from(index.ty)]);

                    Ok((
                        Term::call_no_normalize(
                            self.ctx.tcx,
                            index_logic_method,
                            subst,
                            Box::new([cur, index.clone()]),
                        ),
                        Term::call_no_normalize(
                            self.ctx.tcx,
                            index_logic_method,
                            subst,
                            Box::new([fin, index]),
                        ),
                        inner,
                        proj
                    ))
                } else {
                    Err(Error::msg(span, format!("unsupported projection {id:?}")))
                }
            }
            e => Err(Error::msg(
                span,
                format!("unsupported logical reborrow {e:?}, only field projections and slice indexing are supported"),
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

fn is_ghost_box_deref<'tcx>(
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
            if is_ghost_ty(tcx, containing_type.did()) {
                Some(new_subst)
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(crate) fn mk_projection(lhs: Term, name: FieldIdx) -> TermKind {
    TermKind::Projection { lhs: Box::new(lhs), name }
}

pub(crate) fn type_invariant_term<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    env_did: DefId,
    name: Symbol,
    span: Span,
    ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    // assert!(!name.as_str().is_empty(), "name has len 0, env={env_did:?}, ty={ty:?}");
    let arg = Term { ty, span, kind: TermKind::Var(name) };

    let (inv_fn_did, inv_fn_substs) =
        ctx.type_invariant(TypingEnv::non_body_analysis(ctx.tcx, env_did), ty)?;
    let inv_fn_ty = ctx.type_of(inv_fn_did).instantiate(ctx.tcx, inv_fn_substs);
    assert!(matches!(inv_fn_ty.kind(), TyKind::FnDef(id, _) if id == &inv_fn_did));

    Some(Term {
        ty: ctx.fn_sig(inv_fn_did).skip_binder().output().skip_binder(),
        span,
        kind: TermKind::Call { id: inv_fn_did, subst: inv_fn_substs, args: Box::new([arg]) },
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

pub fn zip_binder<'a, 'tcx>(
    binder: &'a QuantBinder<'tcx>,
) -> impl Iterator<Item = (Symbol, Ty<'tcx>)> + 'a {
    binder.0.iter().map(|x| x.name).zip(binder.1.tuple_fields())
}

impl<'tcx> Pattern<'tcx> {
    pub(crate) fn get_bool(&self) -> Option<bool> {
        match self {
            Pattern::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    pub(crate) fn binds(&self, binders: &mut HashSet<Symbol>) {
        match self {
            Pattern::Constructor { fields, .. } => fields.iter().for_each(|f| f.binds(binders)),
            Pattern::Tuple(fields) => fields.iter().for_each(|f| f.binds(binders)),
            Pattern::Wildcard => {}
            Pattern::Binder(s) => {
                binders.insert(*s);
            }

            Pattern::Boolean(_) => {}
            Pattern::Deref { pointee, .. } => pointee.binds(binders),
        }
    }
}

pub trait TermVisitor<'tcx> {
    fn visit_term(&mut self, term: &Term<'tcx>);
}

pub fn super_visit_term<'tcx, V: TermVisitor<'tcx>>(term: &Term<'tcx>, visitor: &mut V) {
    match &term.kind {
        TermKind::Var(_) => {}
        TermKind::Lit(_) => {}
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
        TermKind::Projection { lhs, name: _ } => visitor.visit_term(lhs),
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
        TermKind::Projection { lhs, name: _ } => visitor.visit_mut_term(&mut *lhs),
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
    pub(crate) fn mk_true(tcx: TyCtxt<'tcx>) -> Self {
        Term { ty: tcx.types.bool, kind: TermKind::Lit(Literal::Bool(true)), span: DUMMY_SP }
    }

    pub(crate) fn mk_false(tcx: TyCtxt<'tcx>) -> Self {
        Term { ty: tcx.types.bool, kind: TermKind::Lit(Literal::Bool(false)), span: DUMMY_SP }
    }

    pub(crate) fn call_no_normalize(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        subst: GenericArgsRef<'tcx>,
        args: Box<[Term<'tcx>]>,
    ) -> Self {
        let ty = tcx.type_of(def_id).instantiate(tcx, subst);
        let result = ty.fn_sig(tcx).skip_binder().output();
        Term { ty: result, span: DUMMY_SP, kind: TermKind::Call { id: def_id, subst, args } }
    }

    pub(crate) fn call(
        tcx: TyCtxt<'tcx>,
        typing_env: TypingEnv<'tcx>,
        def_id: DefId,
        subst: GenericArgsRef<'tcx>,
        args: Box<[Term<'tcx>]>,
    ) -> Self {
        let mut res = Self::call_no_normalize(tcx, def_id, subst, args);
        res.ty = tcx.normalize_erasing_regions(typing_env, res.ty);
        res
    }

    pub(crate) fn var(sym: Symbol, ty: Ty<'tcx>) -> Self {
        Term { ty, kind: TermKind::Var(sym), span: DUMMY_SP }
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
        tcx: TyCtxt<'tcx>,
        binder: (Symbol, Ty<'tcx>),
        trigger: Box<[Trigger<'tcx>]>,
    ) -> Self {
        let ty = Ty::new_tup(tcx, &[binder.1]);
        self.quant(QuantKind::Forall, (Box::new([Ident::new(binder.0, DUMMY_SP)]), ty), trigger)
    }

    pub(crate) fn forall(self, tcx: TyCtxt<'tcx>, binder: (Symbol, Ty<'tcx>)) -> Self {
        self.forall_trig(tcx, binder, Box::new([]))
    }

    pub(crate) fn exists(self, tcx: TyCtxt<'tcx>, binder: (Symbol, Ty<'tcx>)) -> Self {
        let ty = Ty::new_tup(tcx, &[binder.1]);

        self.quant(QuantKind::Exists, (Box::new([Ident::new(binder.0, DUMMY_SP)]), ty), Box::new([]))
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
    pub(crate) fn subst(&mut self, inv_subst: &std::collections::HashMap<Symbol, Term<'tcx>>) {
        self.subst_with(|k| inv_subst.get(&k).cloned());
    }

    pub(crate) fn subst_with<F: FnMut(Symbol) -> Option<Term<'tcx>>>(&mut self, mut f: F) {
        self.subst_with_inner(&HashSet::new(), &mut f)
    }

    fn subst_with_inner<F: FnMut(Symbol) -> Option<Term<'tcx>>>(
        &mut self,
        bound: &HashSet<Symbol>,
        inv_subst: &mut F,
    ) {
        match &mut self.kind {
            TermKind::Var(v) => {
                if bound.contains(v) {
                    return;
                }
                if let Some(t) = inv_subst(*v) {
                    self.kind = t.kind.clone()
                }
            }
            TermKind::Lit(_) => {}
            TermKind::Cast { arg } => arg.subst_with_inner(bound, inv_subst),
            TermKind::Coerce { arg } => arg.subst_with_inner(bound, inv_subst),
            TermKind::Item(_, _) => {}
            TermKind::Binary { lhs, rhs, .. } => {
                lhs.subst_with_inner(bound, inv_subst);
                rhs.subst_with_inner(bound, inv_subst)
            }
            TermKind::Unary { arg, .. } => arg.subst_with_inner(bound, inv_subst),
            TermKind::Quant { binder, body, .. } => {
                let mut bound = bound.clone();
                for name in &binder.0 {
                    bound.insert(name.name);
                }

                body.subst_with_inner(&bound, inv_subst);
            }
            TermKind::Call { args, .. } => {
                args.iter_mut().for_each(|f| f.subst_with_inner(bound, inv_subst))
            }
            TermKind::Constructor { fields, .. } => {
                fields.iter_mut().for_each(|f| f.subst_with_inner(bound, inv_subst))
            }
            TermKind::Tuple { fields } => {
                fields.iter_mut().for_each(|f| f.subst_with_inner(bound, inv_subst))
            }
            TermKind::Cur { term } => term.subst_with_inner(bound, inv_subst),
            TermKind::Fin { term } => term.subst_with_inner(bound, inv_subst),
            TermKind::Impl { lhs, rhs } => {
                lhs.subst_with_inner(bound, inv_subst);
                rhs.subst_with_inner(bound, inv_subst)
            }
            TermKind::Match { scrutinee, arms } => {
                scrutinee.subst_with_inner(bound, inv_subst);
                let mut bound = bound.clone();

                arms.iter_mut().for_each(|(pat, arm)| {
                    pat.binds(&mut bound);
                    arm.subst_with_inner(&bound, inv_subst)
                })
            }
            TermKind::Let { pattern, arg, body } => {
                arg.subst_with_inner(bound, inv_subst);
                let mut bound = bound.clone();
                pattern.binds(&mut bound);
                body.subst_with_inner(&bound, inv_subst);
            }
            TermKind::Projection { lhs, .. } => lhs.subst_with_inner(bound, inv_subst),
            TermKind::Old { term } => term.subst_with_inner(bound, inv_subst),
            TermKind::Closure { body, bound: bound_new } => {
                let mut bound = bound.clone();
                bound.extend(bound_new.iter());
                body.subst_with_inner(&bound, inv_subst);
            }
            TermKind::Reborrow { cur, fin, inner, projection } => {
                cur.subst_with_inner(bound, inv_subst);
                fin.subst_with_inner(bound, inv_subst);
                inner.subst_with_inner(bound, inv_subst);
                visit_projections_mut(projection, |term| term.subst_with_inner(bound, inv_subst))
            }
            TermKind::Assert { cond } => cond.subst_with_inner(bound, inv_subst),
            TermKind::Precondition { params, .. } => {
                params.iter_mut().for_each(|p| p.subst_with_inner(bound, inv_subst))
            }
            TermKind::Postcondition { params, .. } => {
                params.iter_mut().for_each(|p| p.subst_with_inner(bound, inv_subst))
            }
        }
    }

    pub(crate) fn free_vars(&self) -> HashSet<Symbol> {
        let mut free = HashSet::new();
        self.free_vars_inner(&HashSet::new(), &mut free);
        free
    }

    fn free_vars_inner(&self, bound: &HashSet<Symbol>, free: &mut HashSet<Symbol>) {
        match &self.kind {
            TermKind::Var(v) => {
                if !bound.contains(v) {
                    free.insert(*v);
                }
            }
            TermKind::Lit(_) => {}
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
                for name in &binder.0 {
                    bound.insert(name.name);
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
                let mut bound = bound.clone();

                for (pat, arm) in arms {
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
                bound.extend(bound_new.iter());
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
