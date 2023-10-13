// A poorly named module.
//
// Entrypoint for translation of all Pearlite specifications and code: #[ghost] / #[logic], contracts, proof_assert!
//
// Transforms THIR into a Term which may be serialized in Creusot metadata files for usage by dependent crates
// The `lower` module then transforms a `Term` into a WhyML expression.

use std::collections::HashSet;

use crate::{
    error::{CrErr, CreusotResult, Error},
    translation::TranslationCtx,
    util,
};
use itertools::Itertools;
use log::*;
use rustc_ast::{LitIntType, LitKind};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    HirId, OwnerId,
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
pub(crate) use rustc_middle::thir;
use rustc_middle::{
    mir::{BorrowKind, Mutability::*},
    thir::{
        AdtExpr, ArmId, Block, ClosureExpr, ExprId, ExprKind, Pat, PatKind, StmtId, StmtKind, Thir,
    },
    ty::{
        int_ty, subst::SubstsRef, uint_ty, Ty, TyCtxt, TyKind, TypeFoldable, TypeVisitable,
        UpvarSubsts,
    },
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{Span, Symbol, DUMMY_SP};
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

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum TermKind<'tcx> {
    Var(Symbol),
    Lit(Literal<'tcx>),
    Item(DefId, SubstsRef<'tcx>),
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
    Forall {
        binder: (Symbol, Ty<'tcx>),
        body: Box<Term<'tcx>>,
    },
    Exists {
        binder: (Symbol, Ty<'tcx>),
        body: Box<Term<'tcx>>,
    },
    // TODO: Get rid of (id, subst).
    Call {
        id: DefId,
        subst: SubstsRef<'tcx>,
        fun: Box<Term<'tcx>>,
        args: Vec<Term<'tcx>>,
    },
    Constructor {
        typ: DefId,
        variant: VariantIdx,
        fields: Vec<Term<'tcx>>,
    },
    Tuple {
        fields: Vec<Term<'tcx>>,
    },
    // FIXME: Rename to Deref
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
        arms: Vec<(Pattern<'tcx>, Term<'tcx>)>,
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
        body: Box<Term<'tcx>>,
    },
    Reborrow {
        cur: Box<Term<'tcx>>,
        fin: Box<Term<'tcx>>,
    },
    Absurd,
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
    fn visit_with<V: rustc_middle::ty::TypeVisitor<I>>(
        &self,
        _: &mut V,
    ) -> std::ops::ControlFlow<V::BreakTy> {
        ::std::ops::ControlFlow::Continue(())
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
    Bool(bool),
    // TODO: Find a way to make this a BigInt type
    Integer(i128),
    MachSigned(i128, IntTy),
    MachUnsigned(u128, UintTy),
    Float(Float, FloatTy),
    String(String),
    ZST,
    Function(DefId, SubstsRef<'tcx>),
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum Pattern<'tcx> {
    Constructor {
        adt: DefId,
        substs: SubstsRef<'tcx>,
        variant: VariantIdx,
        fields: Vec<Pattern<'tcx>>,
    },
    Tuple(Vec<Pattern<'tcx>>),
    Wildcard,
    Binder(Symbol),
    Boolean(bool),
}

pub(crate) fn pearlite<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: LocalDefId,
) -> CreusotResult<Term<'tcx>> {
    let (thir, expr) = ctx.thir_body(id).map_err(|_| CrErr)?;
    let thir = thir.borrow();
    if thir.exprs.is_empty() {
        return Err(Error::new(ctx.def_span(id), "type checking failed"));
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
    fn body_term(&self, expr: ExprId) -> CreusotResult<Term<'tcx>> {
        let body = self.expr_term(expr)?;
        let owner_id = util::param_def_id(self.ctx.tcx, self.item_id.into());
        let (thir, _) = self.ctx.thir_body(owner_id).map_err(|_| CrErr)?;
        let thir: &Thir = &thir.borrow();
        let res = thir
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                Some(self.pattern_term(&*param.pat.as_ref()?).map(|pat| (idx, param.ty, pat)))
            })
            .fold_ok(body, |body, (idx, ty, pattern)| match pattern {
                Pattern::Binder(_) | Pattern::Wildcard => body,
                _ => {
                    let arg = Box::new(Term::var(util::anonymous_param_symbol(idx), ty));
                    Term {
                        ty: body.ty,
                        span: body.span,
                        kind: TermKind::Let { pattern, arg, body: Box::new(body) },
                    }
                }
            });
        res
    }

    fn expr_term(&self, expr: ExprId) -> CreusotResult<Term<'tcx>> {
        let ty = self.thir[expr].ty;
        let thir_term = &self.thir[expr];
        let span = self.thir[expr].span;
        match thir_term.kind {
            ExprKind::Scope { value, .. } => self.expr_term(value),
            ExprKind::Block { block } => {
                let Block { ref stmts, expr, .. } = self.thir[block];
                let mut inner = match expr {
                    Some(e) => self.expr_term(e)?,
                    None => Term { ty, span, kind: TermKind::Tuple { fields: vec![] } },
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

                use rustc_middle::mir;
                let op = match op {
                    mir::BinOp::Add | mir::BinOp::AddUnchecked => BinOp::Add,
                    mir::BinOp::Sub | mir::BinOp::SubUnchecked => BinOp::Sub,
                    mir::BinOp::Mul | mir::BinOp::MulUnchecked => BinOp::Mul,
                    mir::BinOp::Div => BinOp::Div,
                    mir::BinOp::Rem => BinOp::Rem,
                    mir::BinOp::BitXor => {
                        return Err(Error::new(self.thir[expr].span, "unsupported operation"))
                    }
                    mir::BinOp::BitAnd => {
                        return Err(Error::new(self.thir[expr].span, "unsupported operation"))
                    }
                    mir::BinOp::BitOr => {
                        return Err(Error::new(self.thir[expr].span, "unsupported operation"))
                    }
                    mir::BinOp::Shl | mir::BinOp::ShlUnchecked => {
                        return Err(Error::new(self.thir[expr].span, "unsupported operation"))
                    }
                    mir::BinOp::Shr | mir::BinOp::ShrUnchecked => {
                        return Err(Error::new(self.thir[expr].span, "unsupported operation"))
                    }
                    mir::BinOp::Lt => BinOp::Lt,
                    mir::BinOp::Le => BinOp::Le,
                    mir::BinOp::Ge => BinOp::Ge,
                    mir::BinOp::Gt => BinOp::Gt,
                    mir::BinOp::Ne => unreachable!(),
                    mir::BinOp::Eq => unreachable!(),
                    mir::BinOp::Offset => todo!(),
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
                let op = match op {
                    rustc_middle::mir::UnOp::Not => UnOp::Not,
                    rustc_middle::mir::UnOp::Neg => UnOp::Neg,
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
                    LitKind::Int(u, lty) => match lty {
                        LitIntType::Signed(ity) => {
                            let val = if neg { (u as i128).wrapping_neg() } else { u as i128 };
                            Literal::MachSigned(val, int_ty(ity))
                        }
                        LitIntType::Unsigned(uty) => Literal::MachUnsigned(u, uint_ty(uty)),
                        LitIntType::Unsuffixed => match ty.kind() {
                            TyKind::Int(ity) => {
                                let val = if neg { (u as i128).wrapping_neg() } else { u as i128 };
                                Literal::MachSigned(val, *ity)
                            }
                            TyKind::Uint(uty) => Literal::MachUnsigned(u, *uty),
                            _ => unreachable!(),
                        },
                    },
                    _ => unimplemented!("Unsupported literal"),
                };
                Ok(Term { ty, span, kind: TermKind::Lit(lit) })
            }
            ExprKind::Call { ty: f_ty, fun, ref args, .. } => {
                use Stub::*;
                match pearlite_stub(self.ctx.tcx, f_ty) {
                    Some(Forall) => {
                        let (binder, body) = self.quant_term(args[0])?;
                        if let Some(inv_term) = type_invariant_term(
                            self.ctx,
                            self.item_id.to_def_id(),
                            binder.0,
                            span,
                            binder.1.tuple_fields()[0],
                        ) {
                            Ok(body.guarded_forall(binder, inv_term).span(span))
                        } else {
                            Ok(body.forall(binder).span(span))
                        }
                    }
                    Some(Exists) => {
                        let (binder, body) = self.quant_term(args[0])?;
                        if let Some(inv_term) = type_invariant_term(
                            self.ctx,
                            self.item_id.to_def_id(),
                            binder.0,
                            span,
                            binder.1.tuple_fields()[0],
                        ) {
                            Ok(body.guarded_exists(binder, inv_term).span(span))
                        } else {
                            Ok(body.exists(binder).span(span))
                        }
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
                        Ok(Term { ty, span, kind: TermKind::Tuple { fields: vec![] } })
                    }
                    Some(Absurd) => Ok(Term { ty, span, kind: TermKind::Absurd }),
                    None => {
                        let fun = self.expr_term(fun)?;
                        let args = args
                            .iter()
                            .map(|arg| self.expr_term(*arg))
                            .collect::<Result<Vec<_>, _>>()?;
                        let (id, subst) = if let TyKind::FnDef(id, subst) = f_ty.kind() {
                            (*id, subst)
                        } else {
                            unreachable!("Call on non-function type");
                        };

                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Call { id, subst, fun: Box::new(fun), args },
                        })
                    }
                }
            }
            ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } => self.expr_term(arg),
            ExprKind::Borrow { arg, .. } => {
                let t = self.logical_reborrow(arg)?;
                Ok(Term { ty, span, kind: t })
            }
            ExprKind::Adt(box AdtExpr {
                adt_def,
                variant_index,
                ref fields,
                ref base,
                substs,
                ..
            }) => {
                let mut fields: Vec<_> = fields
                    .iter()
                    .map(|f| Ok((f.name, self.expr_term(f.expr)?)))
                    .collect::<Result<_, Error>>()?;

                if let Some(base) = base {
                    let variant = &adt_def.variant(variant_index);

                    let base = self.expr_term(base.base)?;
                    let missing: Vec<_> = (0..variant.fields.len())
                        .filter(|i| !fields.iter().any(|(f, _)| i == &f.as_usize()))
                        .collect();

                    for missing_field in missing {
                        fields.push((
                            missing_field.into(),
                            Term {
                                ty: variant.fields[missing_field.into()].ty(self.ctx.tcx, substs),
                                span: DUMMY_SP,
                                kind: self.mk_projection(base.clone(), missing_field.into())?,
                            },
                        ));
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
            // TODO: If we deref a shared borrow this should be erased?
            // Can it happen?
            ExprKind::Deref { arg } => {
                let mut arg_trans = self.expr_term(arg)?;
                if self.thir[arg].ty.is_box() || self.thir[arg].ty.ref_mutability() == Some(Not) {
                    arg_trans.ty = arg_trans.ty.builtin_deref(false).expect("expected &T").ty;
                    Ok(arg_trans)
                } else {
                    Ok(Term { ty, span, kind: TermKind::Cur { term: Box::new(arg_trans) } })
                }
            }
            ExprKind::Match { scrutinee, ref arms } => {
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
                    Term { span, ty: self.ctx.types.unit, kind: TermKind::Tuple { fields: vec![] } }
                };
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Match {
                        scrutinee: Box::new(cond),
                        arms: vec![(Pattern::Boolean(true), then), (Pattern::Boolean(false), els)],
                    },
                })
            }
            ExprKind::Field { lhs, name, .. } => {
                let lhs = self.expr_term(lhs)?;
                Ok(Term { ty, span, kind: self.mk_projection(lhs, name)? })
            }
            ExprKind::Tuple { ref fields } => {
                let fields: Vec<_> =
                    fields.iter().map(|f| self.expr_term(*f)).collect::<Result<_, _>>()?;
                Ok(Term { ty, span, kind: TermKind::Tuple { fields } })
            }
            ExprKind::Use { source } => self.expr_term(source),
            ExprKind::NeverToAny { .. } => Ok(Term { ty, span, kind: TermKind::Absurd }),
            ExprKind::ValueTypeAscription { source, .. } => self.expr_term(source),
            ExprKind::Box { value } => self.expr_term(value),
            // ExprKind::Array { ref fields } => todo!("Array {:?}", fields),
            ExprKind::NonHirLiteral { .. } => match ty.kind() {
                TyKind::FnDef(id, substs) => {
                    Ok(Term { ty, span, kind: TermKind::Item(*id, substs) })
                }
                _ => Err(Error::new(thir_term.span, "unhandled literal expression")),
            },
            ExprKind::NamedConst { def_id, substs, .. } => {
                Ok(Term { ty, span, kind: TermKind::Item(def_id, substs) })
            }
            ExprKind::ZstLiteral { .. } => match ty.kind() {
                TyKind::FnDef(def_id, subst) => {
                    Ok(Term { ty, span, kind: TermKind::Item(*def_id, subst) })
                }
                _ => Ok(Term { ty, span, kind: TermKind::Lit(Literal::ZST) }),
            },
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                let term = pearlite(self.ctx, closure_id)?;

                if util::is_assertion(self.ctx.tcx, closure_id.to_def_id()) {
                    Ok(Term { ty, span, kind: TermKind::Assert { cond: Box::new(term) } })
                } else {
                    Ok(Term { ty, span, kind: TermKind::Closure { body: Box::new(term) } })
                }
            }
            ref ek => todo!("lower_expr: {:?}", ek),
        }
    }

    fn arm_term(&self, arm: ArmId) -> CreusotResult<(Pattern<'tcx>, Term<'tcx>)> {
        let arm = &self.thir[arm];

        if arm.guard.is_some() {
            return Err(Error::new(arm.span, "match guards are unsupported"));
        }

        let pattern = self.pattern_term(&arm.pattern)?;
        let body = self.expr_term(arm.body)?;

        Ok((pattern, body))
    }

    fn pattern_term(&self, pat: &Pat<'tcx>) -> CreusotResult<Pattern<'tcx>> {
        trace!("{:?}", pat);
        match &pat.kind {
            PatKind::Wild => Ok(Pattern::Wildcard),
            PatKind::Binding { name, .. } => Ok(Pattern::Binder(*name)),
            PatKind::Variant { subpatterns, adt_def, variant_index, substs, .. } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, self.pattern_term(&pat.pattern)?)))
                    .collect::<Result<_, Error>>()?;
                fields.sort_by_key(|f| f.0);

                let field_count = adt_def.variants()[*variant_index].fields.len();
                let defaults = (0usize..field_count).map(|i| (i.into(), Pattern::Wildcard));

                let fields = defaults
                    .merge_join_by(fields, |i: &(FieldIdx, _), j: &(FieldIdx, _)| i.0.cmp(&j.0))
                    .map(|el| el.reduce(|_, a| a).1)
                    .collect();

                Ok(Pattern::Constructor {
                    adt: adt_def.variants()[*variant_index].def_id,
                    substs,
                    variant: *variant_index,
                    fields,
                })
            }
            PatKind::Leaf { subpatterns } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, self.pattern_term(&pat.pattern)?)))
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
                        adt: adt_def.variants()[0usize.into()].def_id,
                        substs,
                        variant: 0u32.into(),
                        fields,
                    })
                }
            }
            PatKind::Deref { subpattern } => {
                if !(pat.ty.is_box() || pat.ty.ref_mutability() == Some(Not)) {
                    return Err(Error::new(
                        pat.span,
                        "only deref patterns for box and & are supported",
                    ));
                }

                self.pattern_term(subpattern)
            }
            PatKind::Constant { value } => {
                if !pat.ty.is_bool() {
                    return Err(Error::new(
                        pat.span,
                        "non-boolean constant patterns are unsupported",
                    ));
                }
                Ok(Pattern::Boolean(value.try_to_bool().unwrap()))
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
                let pattern = self.pattern_term(pattern)?;
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
                        local_id: init_scope.id,
                    });
                    Err(Error::new(span, "let-bindings must have values"))
                }
            }
        }
    }

    fn quant_term(&self, body: ExprId) -> Result<((Symbol, Ty<'tcx>), Term<'tcx>), Error> {
        trace!("{:?}", self.thir[body].kind);
        match self.thir[body].kind {
            ExprKind::Scope { value, .. } => self.quant_term(value),
            ExprKind::Closure(box ClosureExpr { closure_id, substs, .. }) => {
                let sig = match substs {
                    UpvarSubsts::Closure(subst) => subst.as_closure().sig(),
                    _ => unreachable!(),
                };

                let name = self.ctx.fn_arg_names(closure_id)[0];
                let ty = sig.input(0).skip_binder();

                Ok(((name.name, ty), pearlite(self.ctx, closure_id)?))
            }
            _ => Err(Error::new(self.thir[body].span, "unexpected error in quantifier")),
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
        // Handle every other case.
        let (cur, fin) = self.logical_reborrow_inner(rebor_id)?;

        Ok(TermKind::Reborrow { cur: Box::new(cur), fin: Box::new(fin) })
    }

    fn logical_reborrow_inner(&self, rebor_id: ExprId) -> Result<(Term<'tcx>, Term<'tcx>), Error> {
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
                let (cur, fin) = self.logical_reborrow_inner(*lhs)?;
                Ok((
                    Term { ty, span, kind: self.mk_projection(cur, *name)? },
                    Term { ty, span, kind: self.mk_projection(fin, *name)? },
                ))
            }
            ExprKind::Deref { arg } => {
                let inner = self.expr_term(*arg)?;
                if let TermKind::Var(_) = inner.kind {}
                let ty = inner.ty.builtin_deref(false).expect("expected reference type").ty;

                Ok((
                    Term { ty, span, kind: TermKind::Cur { term: Box::new(inner.clone()) } },
                    Term { ty, span, kind: TermKind::Fin { term: Box::new(inner) } },
                ))
            }
            _ => Err(Error::new(
                span,
                "unsupported logical reborrow, only simple field projections are supproted, sorry",
            )),
        }
    }

    fn mk_projection(&self, lhs: Term<'tcx>, name: FieldIdx) -> Result<TermKind<'tcx>, Error> {
        let pat = field_pattern(lhs.ty, name).expect("mk_projection: no term for field");

        match &lhs.ty.kind() {
            TyKind::Adt(_def, _substs) => Ok(TermKind::Projection { lhs: Box::new(lhs), name }),
            TyKind::Tuple(_) => {
                Ok(TermKind::Let {
                    pattern: pat,
                    // this is the wrong type
                    body: Box::new(Term {
                        ty: lhs.ty,
                        span: rustc_span::DUMMY_SP,
                        kind: TermKind::Var(Symbol::intern("a")),
                    }),
                    arg: Box::new(lhs),
                })
            }
            _ => unreachable!(),
        }
    }
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

    let (inv_fn_did, inv_fn_substs) = ctx.type_invariant(env_did, ty)?;
    let inv_fn_ty = ctx.type_of(inv_fn_did).subst(ctx.tcx, inv_fn_substs);
    assert!(matches!(inv_fn_ty.kind(), TyKind::FnDef(id, _) if id == &inv_fn_did));

    let fun = Term { ty: inv_fn_ty, span, kind: TermKind::Item(inv_fn_did, inv_fn_substs) };
    Some(Term {
        ty: ctx.fn_sig(inv_fn_did).skip_binder().output().skip_binder(),
        span,
        kind: TermKind::Call {
            id: inv_fn_did,
            subst: inv_fn_substs,
            fun: Box::new(fun),
            args: vec![arg],
        },
    })
}

#[derive(Debug)]
pub(crate) enum Stub {
    Forall,
    Exists,
    Fin,
    Impl,
    Equals,
    Neq,
    VariantCheck,
    Old,
    ResultCheck,
    Absurd,
}

pub(crate) fn pearlite_stub<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Stub> {
    if let TyKind::FnDef(id, _) = ty.kind() {
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("forall")) {
            return Some(Stub::Forall);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("exists")) {
            return Some(Stub::Exists);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("fin")) {
            return Some(Stub::Fin);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("implication")) {
            return Some(Stub::Impl);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("equal")) {
            return Some(Stub::Equals);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("neq")) {
            return Some(Stub::Neq);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("variant_check")) {
            return Some(Stub::VariantCheck);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("old")) {
            return Some(Stub::Old);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("absurd")) {
            return Some(Stub::Absurd);
        }
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("closure_result_constraint")) {
            return Some(Stub::ResultCheck);
        }
        None
    } else {
        None
    }
}

fn field_pattern(ty: Ty, field: FieldIdx) -> Option<Pattern> {
    match ty.kind() {
        TyKind::Tuple(fields) => {
            let mut fields: Vec<_> = (0..fields.len()).map(|_| Pattern::Wildcard).collect();
            fields[field.as_usize()] = Pattern::Binder(Symbol::intern("a"));

            Some(Pattern::Tuple(fields))
        }
        TyKind::Adt(ref adt, substs) => {
            assert!(adt.is_struct(), "can only access fields of struct types");
            assert_eq!(adt.variants().len(), 1, "expected a single variant");
            let variant = &adt.variants()[0u32.into()];

            let mut fields: Vec<_> = (0..variant.fields.len()).map(|_| Pattern::Wildcard).collect();
            fields[field.as_usize()] = Pattern::Binder(Symbol::intern("a"));

            Some(Pattern::Constructor {
                adt: variant.def_id,
                substs,
                variant: 0usize.into(),
                fields,
            })
        }
        _ => unreachable!("field_pattern: {:?}", ty),
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
            !util::is_spec(tcx, closure_id.to_def_id())
        }
        _ => true,
    }
}

use rustc_hir;

impl<'tcx> Pattern<'tcx> {
    pub(crate) fn binds(&self, binders: &mut HashSet<Symbol>) {
        match self {
            Pattern::Constructor { fields, .. } => fields.iter().for_each(|f| f.binds(binders)),
            Pattern::Tuple(fields) => fields.iter().for_each(|f| f.binds(binders)),
            Pattern::Wildcard => {}
            Pattern::Binder(s) => {
                binders.insert(*s);
            }

            Pattern::Boolean(_) => {}
        }
    }
}

pub trait TermVisitor<'tcx> {
    fn visit_term(&mut self, term: &Term<'tcx>);
}

#[allow(dead_code)]
pub fn super_visit_term<'tcx, V: TermVisitor<'tcx>>(term: &Term<'tcx>, visitor: &mut V) {
    match &term.kind {
        TermKind::Var(_) => {}
        TermKind::Lit(_) => {}
        TermKind::Item(_, _) => {}
        TermKind::Binary { op: _, lhs, rhs } => {
            visitor.visit_term(&*lhs);
            visitor.visit_term(&*rhs);
        }
        TermKind::Unary { op: _, arg } => visitor.visit_term(&*arg),
        TermKind::Forall { binder: _, body } => visitor.visit_term(&*body),
        TermKind::Exists { binder: _, body } => visitor.visit_term(&*body),
        TermKind::Call { id: _, subst: _, fun, args } => {
            visitor.visit_term(&*fun);
            args.iter().for_each(|a| visitor.visit_term(&*a))
        }
        TermKind::Constructor { typ: _, variant: _, fields } => {
            fields.iter().for_each(|a| visitor.visit_term(&*a))
        }
        TermKind::Tuple { fields } => fields.iter().for_each(|a| visitor.visit_term(&*a)),
        TermKind::Cur { term } => visitor.visit_term(&*term),
        TermKind::Fin { term } => visitor.visit_term(&*term),
        TermKind::Impl { lhs, rhs } => {
            visitor.visit_term(&*lhs);
            visitor.visit_term(&*rhs)
        }
        TermKind::Match { scrutinee, arms } => {
            visitor.visit_term(&*scrutinee);
            arms.iter().for_each(|(_, arm)| visitor.visit_term(&*arm))
        }
        TermKind::Let { pattern: _, arg, body } => {
            visitor.visit_term(&*arg);
            visitor.visit_term(&*body)
        }
        TermKind::Projection { lhs, name: _ } => visitor.visit_term(&*lhs),
        TermKind::Old { term } => visitor.visit_term(&*term),
        TermKind::Closure { body } => visitor.visit_term(&*body),
        TermKind::Absurd => {}
        TermKind::Reborrow { cur, fin } => {
            visitor.visit_term(&*cur);
            visitor.visit_term(&*fin)
        }
        TermKind::Assert { cond } => visitor.visit_term(&*cond),
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
        TermKind::Item(_, _) => {}
        TermKind::Binary { op: _, lhs, rhs } => {
            visitor.visit_mut_term(&mut *lhs);
            visitor.visit_mut_term(&mut *rhs);
        }
        TermKind::Unary { op: _, arg } => visitor.visit_mut_term(&mut *arg),
        TermKind::Forall { binder: _, body } => visitor.visit_mut_term(&mut *body),
        TermKind::Exists { binder: _, body } => visitor.visit_mut_term(&mut *body),
        TermKind::Call { id: _, subst: _, fun, args } => {
            visitor.visit_mut_term(&mut *fun);
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
        TermKind::Closure { body } => visitor.visit_mut_term(&mut *body),
        TermKind::Absurd => {}
        TermKind::Reborrow { cur, fin } => {
            visitor.visit_mut_term(&mut *cur);
            visitor.visit_mut_term(&mut *fin)
        }
        TermKind::Assert { cond } => visitor.visit_mut_term(&mut *cond),
    }
}

impl<'tcx> Term<'tcx> {
    pub(crate) fn mk_true(tcx: TyCtxt<'tcx>) -> Self {
        Term { ty: tcx.types.bool, kind: TermKind::Lit(Literal::Bool(true)), span: DUMMY_SP }
    }

    pub(crate) fn mk_false(tcx: TyCtxt<'tcx>) -> Self {
        Term { ty: tcx.types.bool, kind: TermKind::Lit(Literal::Bool(false)), span: DUMMY_SP }
    }

    pub(crate) fn var(sym: Symbol, ty: Ty<'tcx>) -> Self {
        Term { ty, kind: TermKind::Var(sym), span: DUMMY_SP }
    }

    pub(crate) fn cur(self) -> Self {
        assert!(self.ty.is_ref(), "cannot dereference type {:?}", self.ty);

        Term {
            ty: self.ty.builtin_deref(false).unwrap().ty,
            span: self.span,
            kind: TermKind::Cur { term: Box::new(self) },
        }
    }

    pub(crate) fn fin(self) -> Self {
        assert!(self.ty.is_mutable_ptr() && self.ty.is_ref(), "cannot final type {:?}", self.ty);

        Term {
            ty: self.ty.builtin_deref(false).unwrap().ty,
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

    pub(crate) fn item(tcx: TyCtxt<'tcx>, id: DefId, subst: SubstsRef<'tcx>) -> Self {
        Term {
            ty: tcx.type_of(id).subst(tcx, subst),
            kind: TermKind::Item(id, subst),
            span: DUMMY_SP,
        }
    }

    pub(crate) fn eq(tcx: TyCtxt<'tcx>, lhs: Self, rhs: Self) -> Self {
        Term {
            ty: tcx.types.bool,
            kind: TermKind::Binary { op: BinOp::Eq, lhs: Box::new(lhs), rhs: Box::new(rhs) },
            span: DUMMY_SP,
        }
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

    pub(crate) fn forall(self, binder: (Symbol, Ty<'tcx>)) -> Self {
        assert!(self.ty.is_bool());

        // ∀ x . ⟙ = ⟙
        if let TermKind::Lit(Literal::Bool(true)) = self.kind {
            return self;
        };

        Term {
            ty: self.ty,
            kind: TermKind::Forall { binder, body: Box::new(self) },
            span: DUMMY_SP,
        }
    }

    /// Creates a term like `forall<binder> guard ==> self`.
    pub(crate) fn guarded_forall(mut self, binder: (Symbol, Ty<'tcx>), guard: Self) -> Self {
        assert!(self.ty.is_bool() && guard.ty.is_bool());

        let mut inner = &mut self;
        while let TermKind::Forall { ref mut body, .. } = inner.kind {
            // TODO check binder not free in guard
            inner = body
        }

        *inner = guard.implies(inner.clone());
        self.forall(binder)
    }

    pub(crate) fn exists(self, binder: (Symbol, Ty<'tcx>)) -> Self {
        assert!(self.ty.is_bool());

        // ∃ x . ⟘ = ⟘
        if let TermKind::Lit(Literal::Bool(false)) = self.kind {
            return self;
        };

        Term {
            ty: self.ty,
            kind: TermKind::Exists { binder, body: Box::new(self) },
            span: DUMMY_SP,
        }
    }

    /// Creates a term like `exists<binder> guard && self`.
    pub(crate) fn guarded_exists(mut self, binder: (Symbol, Ty<'tcx>), guard: Self) -> Self {
        assert!(self.ty.is_bool() && guard.ty.is_bool());

        let mut inner = &mut self;
        while let TermKind::Exists { ref mut body, .. } = inner.kind {
            // TODO check binder not free in guard
            inner = body
        }

        *inner = guard.conj(inner.clone());
        self.exists(binder)
    }

    pub(crate) fn span(mut self, sp: Span) -> Self {
        self.span = sp;
        self
    }

    pub(crate) fn subst(&mut self, inv_subst: &std::collections::HashMap<Symbol, Term<'tcx>>) {
        self.subst_with(|k| inv_subst.get(&k).cloned());
    }

    pub(crate) fn subst_with<F: FnMut(Symbol) -> Option<Term<'tcx>>>(&mut self, mut f: F) {
        self.subst_with_inner(&mut HashSet::new(), &mut f)
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
                match inv_subst(*v) {
                    Some(t) => self.kind = t.kind.clone(),
                    None => (),
                }
            }
            TermKind::Lit(_) => {}
            TermKind::Item(_, _) => {}
            TermKind::Binary { lhs, rhs, .. } => {
                lhs.subst_with_inner(bound, inv_subst);
                rhs.subst_with_inner(bound, inv_subst)
            }
            TermKind::Unary { arg, .. } => arg.subst_with_inner(bound, inv_subst),
            TermKind::Forall { binder, body } => {
                let mut bound = bound.clone();
                bound.insert(binder.0);

                body.subst_with_inner(&bound, inv_subst);
            }
            TermKind::Exists { binder, body } => {
                let mut bound = bound.clone();
                bound.insert(binder.0);

                body.subst_with_inner(&bound, inv_subst);
            }
            TermKind::Call { fun, args, .. } => {
                fun.subst_with_inner(bound, inv_subst);
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
            TermKind::Closure { body } => {
                body.subst_with_inner(&bound, inv_subst);
            }
            TermKind::Absurd => {}
            TermKind::Reborrow { cur, fin } => {
                cur.subst_with_inner(bound, inv_subst);
                fin.subst_with_inner(bound, inv_subst)
            }
            TermKind::Assert { cond } => cond.subst_with_inner(bound, inv_subst),
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
            TermKind::Item(_, _) => {}
            TermKind::Binary { lhs, rhs, .. } => {
                lhs.free_vars_inner(bound, free);
                rhs.free_vars_inner(bound, free)
            }
            TermKind::Unary { arg, .. } => arg.free_vars_inner(bound, free),
            TermKind::Forall { binder, body } => {
                let mut bound = bound.clone();
                bound.insert(binder.0);

                body.free_vars_inner(&bound, free);
            }
            TermKind::Exists { binder, body } => {
                let mut bound = bound.clone();
                bound.insert(binder.0);

                body.free_vars_inner(&bound, free);
            }
            TermKind::Call { fun, args, .. } => {
                fun.free_vars_inner(bound, free);
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
            TermKind::Closure { body } => {
                body.free_vars_inner(&bound, free);
            }
            TermKind::Absurd => {}
            TermKind::Reborrow { cur, fin } => {
                cur.free_vars_inner(bound, free);
                fin.free_vars_inner(bound, free)
            }
            TermKind::Assert { cond } => cond.free_vars_inner(bound, free),
        }
    }
}
