use crate::{
    contracts_items::{Intrinsic, is_assertion, is_logic_closure, is_spec},
    ctx::TranslationCtx,
    error::{CreusotResult, Error},
    translation::pearlite::{
        BinOp, Ident, Literal, PIdent, Pattern, PatternKind, QuantKind, Term, TermKind, Trigger,
        UnOp,
    },
};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::{ByRef, LitIntType, LitKind, Mutability};
use rustc_hir::{HirId, OwnerId, def::DefKind, def_id::LocalDefId};
use rustc_hir_typeck::expr_use_visitor::PlaceBase;
use rustc_middle::{
    hir::place::ProjectionKind,
    mir::{BorrowKind, ProjectionElem},
    thir::{
        self, AdtExpr, ArmId, Block, ClosureExpr, ExprId, ExprKind, LocalVarId, Pat, PatKind,
        StmtId, StmtKind, Thir,
    },
    ty::{CapturedPlace, Ty, TyKind, TypingEnv, adjustment::PointerCoercion},
};
use rustc_span::sym;
use std::{
    assert_matches::assert_matches,
    fmt::{Display, Formatter},
};

const TRIGGER_ERROR: &str = "Triggers can only be used inside quantifiers";

/// Get a Pearlite term together with its free variables.
pub(crate) fn from_thir<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: LocalDefId,
) -> CreusotResult<(Box<[(PIdent, Ty<'tcx>)]>, Term<'tcx>)> {
    let (bound, triggers, term) = from_thir_with_triggers(ctx, id)?;
    if !triggers.is_empty() {
        Err(Error::msg(ctx.def_span(id), TRIGGER_ERROR))
    } else {
        Ok((bound, term))
    }
}

fn from_thir_with_triggers<'tcx>(
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
        match self.head(expr).kind {
            ExprKind::Call { ty, ref args, .. } => {
                if let TyKind::FnDef(id, _) = *ty.kind()
                    && Intrinsic::Trigger.is(self.ctx, id)
                {
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

    fn head(&self, expr: ExprId) -> &thir::Expr<'tcx> {
        let e = &self.thir[expr];
        match e.kind {
            ExprKind::Scope { value, .. } => self.head(value),
            // `*&expr` is identical to `expr` in Pearlite
            ExprKind::Deref { arg }
                if let ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } =
                    self.head(arg).kind =>
            {
                assert_eq!(self.thir[arg].ty, e.ty);
                self.head(arg)
            }
            _ => e,
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
        match self.head(id).kind {
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                let closure_id = closure_id.to_def_id();
                !is_spec(self.ctx.tcx, closure_id) || is_assertion(self.ctx.tcx, closure_id)
            }
            _ => true,
        }
    }

    /// Translate a THIR expression into a term.
    fn expr_term(&self, expr: ExprId) -> CreusotResult<Term<'tcx>> {
        let thir::Expr { span, ty, ref kind, .. } = *self.head(expr);
        if let Some(p) = self.to_capture(expr) {
            return Ok(Term { kind: TermKind::Capture(p), ty, span });
        }
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
            ExprKind::Call { ty: f_ty, ref args, .. } => {
                let TyKind::FnDef(id, subst) = *f_ty.kind() else {
                    unreachable!("Call on non-function type");
                };
                match self.ctx.intrinsic(id) {
                    s @ (Intrinsic::Forall | Intrinsic::Exists) => {
                        let kind = if let Intrinsic::Forall = s {
                            QuantKind::Forall
                        } else {
                            QuantKind::Exists
                        };
                        let (binder, trigger, body) = self.quant_term(args[0])?;
                        Ok(body.quant(kind, binder, trigger).span(span))
                    }
                    Intrinsic::Implication => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;
                        Ok(lhs.implies(rhs).span(span))
                    }
                    Intrinsic::Equal => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;
                        Ok(lhs.eq(self.ctx.tcx, rhs).span(span))
                    }
                    Intrinsic::Neq => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;
                        Ok(lhs.bin_op(ty, BinOp::Ne, rhs).span(span))
                    }
                    Intrinsic::VariantCheck => self.expr_term(args[0]),
                    Intrinsic::Old => {
                        let term = self.expr_term(args[0])?;
                        Ok(Term { ty, span, kind: TermKind::Old { term: Box::new(term) } })
                    }
                    Intrinsic::ClosureResult => Ok(Term::unit(self.ctx.tcx).span(span)),
                    Intrinsic::Dead => Err(Error::msg(
                        span,
                        "The `dead` term can only be used for the body of trusted logical functions",
                    )),
                    Intrinsic::Trigger => Err(Error::msg(
                        span,
                        "Triggers can only be used directly inside quantifiers",
                    )),
                    Intrinsic::SeqLiteral => {
                        // SeqLiteral is generated by the `seq!` macro.
                        // A call must look like `seq_literal!(&[x,y,z])`.
                        let mut term = args[0];
                        // Peel off everything to get to the array literal
                        let items = loop {
                            match &self.head(term).kind {
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
                    Intrinsic::IndexLogicStub => {
                        let term = self.expr_term(args[0])?;
                        let idx = self.expr_term(args[1])?;
                        Ok(Term::call_no_normalize(
                            self.ctx.tcx,
                            Intrinsic::IndexLogic.get(self.ctx),
                            subst,
                            [term, idx],
                        )
                        .span(span))
                    }
                    Intrinsic::ViewStub => {
                        let term = self.expr_term(args[0])?;
                        Ok(Term::call_no_normalize(
                            self.ctx.tcx,
                            Intrinsic::View.get(self.ctx),
                            subst,
                            [term],
                        )
                        .span(span))
                    }
                    _ if self.ctx.is_diagnostic_item(sym::deref_method, id)
                        && let Some(adt) = subst.type_at(0).ty_adt_def()
                        && Intrinsic::Ghost.is(self.ctx, adt.did()) =>
                    {
                        // Allow dereferencing of `Ghost` in pearlite
                        Ok(self.expr_term(args[0])?.coerce(ty).span(span))
                    }
                    _ => {
                        let args: Box<[_]> = args
                            .iter()
                            .map(|arg| self.expr_term(*arg))
                            .collect::<Result<_, _>>()?;
                        Ok(Term::call_no_normalize(self.ctx.tcx, id, subst, args).span(span))
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
            ExprKind::Deref { arg }
                if let ExprKind::Call { ty, ref args, .. } = self.head(arg).kind
                    && let &TyKind::FnDef(f_did, subst) = ty.kind()
                    && self.ctx.is_diagnostic_item(sym::deref_mut_method, f_did)
                    && let ExprKind::Borrow { borrow_kind, arg } = self.head(args[0]).kind =>
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
                let (bound, term) = from_thir(self.ctx, closure_id)?;

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
        let e = self.head(body);
        trace!("{:?}", e.kind);
        match e.kind {
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                from_thir_with_triggers(self.ctx, closure_id)
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
        let (inner, projections) = self.logical_reborrow_inner(rebor_id)?;
        if projections.is_empty() {
            return Ok(inner.kind);
        }
        Ok(TermKind::Reborrow { inner: Box::new(inner), projections: projections.into() })
    }

    fn logical_reborrow_inner(
        &self,
        rebor_id: ExprId,
    ) -> Result<(Term<'tcx>, Vec<ProjectionElem<Term<'tcx>, Ty<'tcx>>>), Error> {
        let thir::Expr { ty, span, ref kind, .. } = *self.head(rebor_id);
        if self.to_capture(rebor_id).is_some() {
            return Err(Error::msg(
                span,
                format!(
                    "Logical reborrow of a partial capture is not possible, because the prophecy of the captured borrow is not visible within the closure."
                ),
            ));
        }
        match *kind {
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
                    if let ExprKind::Call { ty, ref args, .. } = self.head(arg).kind
                        && let &TyKind::FnDef(f_did, subst) = ty.kind()
                        && self.ctx.is_diagnostic_item(sym::deref_method, f_did)
                        && let ExprKind::Borrow { borrow_kind, arg } = self.head(args[0]).kind =>
                {
                    assert_matches!(borrow_kind, BorrowKind::Shared);
                    assert_matches!(subst.type_at(0).kind(),
                        TyKind::Adt(adt, _) if matches!(self.ctx.intrinsic(adt.did()), Intrinsic::Snapshot | Intrinsic::Ghost));

                    // We have just detected * deref &. Only possible with Ghost and Deref. Replace with deref_mut on the fly.
                    let arg = Term {
                        kind: self.logical_reborrow(arg)?,
                        ty: Ty::new_ref(
                            self.ctx.tcx,
                            self.ctx.lifetimes.re_erased,
                            subst.type_at(0),
                            Mutability::Mut,
                        ),
                        span: self.thir[arg].span,
                    };
                    let did = self.ctx.get_diagnostic_item(sym::deref_mut_method).unwrap();
                    return Ok((
                        Term::call_no_normalize(self.ctx.tcx, did, subst, [arg]).span(span),
                        Vec::new(),
                    ));
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
                    && matches!(
                        self.ctx.intrinsic(*id),
                        Intrinsic::IndexLogic | Intrinsic::IndexLogicStub
                    ) =>
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
                "Unsupported logical reborrow: {kind:?}, only field projections and slice indexing are supported"
            ),
        ))
    }

    // Tries to convert the term into a place that could be captured by a closure
    fn to_hir_place(&self, id: ExprId) -> Option<(LocalVarId, Vec<ProjectionKind>)> {
        let thir::Expr { ref kind, .. } = *self.head(id);
        match *kind {
            ExprKind::UpvarRef { var_hir_id, .. } => Some((var_hir_id, vec![])),
            ExprKind::Deref { arg } => {
                let (base, mut projs) = self.to_hir_place(arg)?;
                projs.push(ProjectionKind::Deref);
                Some((base, projs))
            }
            ExprKind::Field { lhs, variant_index, name } => {
                let (base, mut projs) = self.to_hir_place(lhs)?;
                projs.push(ProjectionKind::Field(name, variant_index));
                Some((base, projs))
            }
            _ => None,
        }
    }

    fn to_capture(&self, id: ExprId) -> Option<FieldIdx> {
        let (base, projs) = self.to_hir_place(id)?;
        let mut enclosing_closure_did = self.item_id;
        loop {
            if self.ctx.def_kind(enclosing_closure_did) != DefKind::Closure {
                return None;
            }
            if !is_logic_closure(self.ctx.tcx, enclosing_closure_did.into())
                && !is_spec(self.ctx.tcx, enclosing_closure_did.into())
            {
                break;
            }
            enclosing_closure_did = self.ctx.opt_local_parent(enclosing_closure_did)?;
        }

        'captures: for (ix, &CapturedPlace { place, .. }) in
            self.ctx.closure_captures(enclosing_closure_did).iter().enumerate()
        {
            match place.base {
                PlaceBase::Local(id) if id == base.0 => (),
                PlaceBase::Upvar(upvar_id) if upvar_id.var_path.hir_id == base.0 => (),
                _ => continue,
            }
            if place.projections.len() != projs.len() {
                continue;
            }
            for (p1, &p2) in place.projections.iter().zip(&projs) {
                if p1.kind != p2 {
                    continue 'captures;
                }
            }
            return Some(ix.into());
        }

        None
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
