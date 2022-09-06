// A poorly named module.
//
// Entrypoint for translation of all Pearlite specifications and code: #[logic] / #[predicate], contracts, proof_assert!
//
// Transforms THIR into a Term which may be serialized in Creusot metadata files for usage by dependent crates
// The `lower` module then transforms a `Term` into a WhyML expression.

use std::collections::HashSet;

use crate::{
    error::{CrErr, CreusotResult, Error},
    util,
};
use creusot_rustc::{
    ast::{LitIntType, LitKind},
    hir::{
        def_id::{DefId, LocalDefId},
        HirId,
    },
    macros::{Decodable, Encodable, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable},
    middle::{
        mir::Mutability::*,
        thir::{visit, Adt, ArmId, Block, ExprId, ExprKind, Pat, PatKind, StmtId, StmtKind, Thir},
        ty::{
            int_ty, subst::SubstsRef, uint_ty, AdtDef, Ty, TyCtxt, TyKind, TypeFoldable,
            TypeVisitable, UpvarSubsts, WithOptConstParam,
        },
    },
    smir::mir::BorrowKind,
    span::{Span, Symbol},
    target::abi::VariantIdx,
};
pub use creusot_rustc::{middle::thir, smir::mir::Field};
use itertools::Itertools;
use log::*;
use rustc_type_ir::{IntTy, UintTy};

use super::PurityVisitor;

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
    Lit(Literal),
    Item(DefId, SubstsRef<'tcx>),
    Binary { op: BinOp, lhs: Box<Term<'tcx>>, rhs: Box<Term<'tcx>> },
    Unary { op: UnOp, arg: Box<Term<'tcx>> },
    Forall { binder: (Symbol, Ty<'tcx>), body: Box<Term<'tcx>> },
    Exists { binder: (Symbol, Ty<'tcx>), body: Box<Term<'tcx>> },
    // TODO: Get rid of (id, subst).
    Call { id: DefId, subst: SubstsRef<'tcx>, fun: Box<Term<'tcx>>, args: Vec<Term<'tcx>> },
    Constructor { adt: AdtDef<'tcx>, variant: VariantIdx, fields: Vec<Term<'tcx>> },
    Tuple { fields: Vec<Term<'tcx>> },
    Cur { term: Box<Term<'tcx>> },
    Fin { term: Box<Term<'tcx>> },
    Impl { lhs: Box<Term<'tcx>>, rhs: Box<Term<'tcx>> },
    Match { scrutinee: Box<Term<'tcx>>, arms: Vec<(Pattern<'tcx>, Term<'tcx>)> },
    Let { pattern: Pattern<'tcx>, arg: Box<Term<'tcx>>, body: Box<Term<'tcx>> },
    Projection { lhs: Box<Term<'tcx>>, name: Field, def: DefId },
    Old { term: Box<Term<'tcx>> },
    Closure { args: Vec<Pattern<'tcx>>, body: Box<Term<'tcx>> },
    Absurd,
}
impl<'tcx> TypeFoldable<'tcx> for Literal {
    fn try_fold_with<F: creusot_rustc::middle::ty::FallibleTypeFolder<'tcx>>(
        self,
        _: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(self)
    }
}

impl<'tcx> TypeVisitable<'tcx> for Literal {
    fn visit_with<V: creusot_rustc::middle::ty::TypeVisitor<'tcx>>(
        &self,
        _: &mut V,
    ) -> std::ops::ControlFlow<V::BreakTy> {
        ::std::ops::ControlFlow::CONTINUE
    }
}

#[derive(Clone, Debug, Decodable, Encodable)]
pub enum Literal {
    Bool(bool),
    Int(i128, IntTy),
    Uint(u128, UintTy),
    Float(f64),
    String(String),
    ZST,
    Function,
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum Pattern<'tcx> {
    Constructor { adt: AdtDef<'tcx>, variant: VariantIdx, fields: Vec<Pattern<'tcx>> },
    Tuple(Vec<Pattern<'tcx>>),
    Wildcard,
    Binder(Symbol),
    Boolean(bool),
}

pub fn typecheck(tcx: TyCtxt, id: LocalDefId) -> CreusotResult<Term> {
    let (thir, expr) = tcx.thir_body(WithOptConstParam::unknown(id)).map_err(|_| CrErr)?;
    let thir = thir.borrow();
    if thir.exprs.is_empty() {
        return Err(Error::new(tcx.def_span(id), "type checking failed"));
    };

    visit::walk_expr(&mut PurityVisitor { tcx, thir: &thir }, &thir[expr]);

    let lower = ThirTerm { tcx, item_id: id, thir: &thir };

    lower.expr_term(expr)
}

struct ThirTerm<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    item_id: LocalDefId,
    thir: &'a Thir<'tcx>,
}

impl<'a, 'tcx> ThirTerm<'a, 'tcx> {
    fn expr_term(&self, expr: ExprId) -> CreusotResult<Term<'tcx>> {
        let ty = self.thir[expr].ty;
        let thir_term = &self.thir[expr];
        let span = self.thir[expr].span;
        match thir_term.kind {
            ExprKind::Scope { value, .. } => self.expr_term(value),
            ExprKind::Block { body: Block { ref stmts, expr, .. } } => {
                let mut inner = match expr {
                    Some(e) => self.expr_term(e)?,
                    None => Term { ty, span, kind: TermKind::Tuple { fields: vec![] } },
                };

                for stmt in stmts.iter().rev().filter(|id| not_spec(self.tcx, self.thir, **id)) {
                    inner = self.stmt_term(*stmt, inner)?;
                }
                Ok(inner)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.expr_term(lhs)?;
                let rhs = self.expr_term(rhs)?;

                use creusot_rustc::middle::mir;
                let op = match op {
                    mir::BinOp::Add => BinOp::Add,
                    mir::BinOp::Sub => BinOp::Sub,
                    mir::BinOp::Mul => BinOp::Mul,
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
                    mir::BinOp::Shl => {
                        return Err(Error::new(self.thir[expr].span, "unsupported operation"))
                    }
                    mir::BinOp::Shr => {
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
                Ok(Term { ty, span, kind: TermKind::Binary { op, lhs: box lhs, rhs: box rhs } })
            }
            ExprKind::LogicalOp { op, lhs, rhs } => {
                let lhs = self.expr_term(lhs)?;
                let rhs = self.expr_term(rhs)?;
                let op = match op {
                    thir::LogicalOp::And => BinOp::And,
                    thir::LogicalOp::Or => BinOp::Or,
                };
                Ok(Term { ty, span, kind: TermKind::Binary { op, lhs: box lhs, rhs: box rhs } })
            }
            ExprKind::Unary { op, arg } => {
                let arg = self.expr_term(arg)?;
                let op = match op {
                    creusot_rustc::middle::mir::UnOp::Not => UnOp::Not,
                    creusot_rustc::middle::mir::UnOp::Neg => UnOp::Neg,
                };
                Ok(Term { ty, span, kind: TermKind::Unary { op, arg: box arg } })
            }
            ExprKind::VarRef { id } => {
                let map = self.tcx.hir();
                let name = map.name(id.0);
                Ok(Term { ty, span, kind: TermKind::Var(name) })
            }
            // TODO: confirm this works
            ExprKind::UpvarRef { var_hir_id: id, .. } => {
                let map = self.tcx.hir();
                let name = map.name(id.0);

                Ok(Term { ty, span, kind: TermKind::Var(name) })
            }
            ExprKind::Literal { lit, neg } => {
                let lit = match lit.node {
                    LitKind::Bool(b) => Literal::Bool(b),
                    LitKind::Int(u, lty) => match lty {
                        LitIntType::Signed(ity) => {
                            let val = if neg { (u as i128).wrapping_neg() } else { u as i128 };
                            Literal::Int(val, int_ty(ity))
                        }
                        LitIntType::Unsigned(uty) => Literal::Uint(u, uint_ty(uty)),
                        LitIntType::Unsuffixed => match ty.kind() {
                            TyKind::Int(ity) => {
                                let val = if neg { (u as i128).wrapping_neg() } else { u as i128 };
                                Literal::Int(val, *ity)
                            }
                            TyKind::Uint(uty) => Literal::Uint(u, *uty),
                            _ => unreachable!(),
                        },
                    },
                    _ => unimplemented!("Unsupported literal"),
                };
                Ok(Term { ty, span, kind: TermKind::Lit(lit) })
            }
            ExprKind::Call { ty: f_ty, fun, ref args, .. } => {
                use Stub::*;
                match pearlite_stub(self.tcx, f_ty) {
                    Some(Forall) => {
                        let (binder, body) = self.quant_term(args[0])?;
                        Ok(Term { ty, span, kind: TermKind::Forall { binder, body: box body } })
                    }
                    Some(Exists) => {
                        let (binder, body) = self.quant_term(args[0])?;
                        Ok(Term { ty, span, kind: TermKind::Exists { binder, body: box body } })
                    }
                    Some(Fin) => {
                        let term = self.expr_term(args[0])?;

                        Ok(Term { ty, span, kind: TermKind::Fin { term: box term } })
                    }
                    Some(Cur) => {
                        let term = self.expr_term(args[0])?;

                        Ok(Term { ty, span, kind: TermKind::Cur { term: box term } })
                    }
                    Some(Impl) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;

                        Ok(Term { ty, span, kind: TermKind::Impl { lhs: box lhs, rhs: box rhs } })
                    }
                    Some(Equals) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;

                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Binary { op: BinOp::Eq, lhs: box lhs, rhs: box rhs },
                        })
                    }
                    Some(Neq) => {
                        let lhs = self.expr_term(args[0])?;
                        let rhs = self.expr_term(args[1])?;

                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Binary { op: BinOp::Ne, lhs: box lhs, rhs: box rhs },
                        })
                    }
                    Some(VariantCheck) => self.expr_term(args[0]),
                    Some(Old) => {
                        let term = self.expr_term(args[0])?;

                        Ok(Term { ty, span, kind: TermKind::Old { term: box term } })
                    }
                    Some(ResultCheck) => {
                        Ok(Term { ty, span, kind: TermKind::Tuple { fields: vec![] } })
                    }
                    Some(DummyCall) => {
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
                            kind: TermKind::Call { id, subst, fun: box fun, args },
                        })
                    }
                }
            }
            ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } => self.expr_term(arg),
            ExprKind::Borrow { arg, .. } => {
                // Rust will introduce add unnecessary reborrows to code.
                // Since we've syntactically ruled out borrowing at a higher level, we should
                // be able erase it safely (:fingers_crossed:)
                if let ExprKind::Deref { arg } = self.thir[arg].kind {
                    self.expr_term(arg)
                } else {
                    Err(Error::new(self.thir[arg].span, "cannot perform a mutable borrow"))
                }
            }
            ExprKind::Adt(box Adt { adt_def, variant_index, ref fields, .. }) => {
                let mut fields: Vec<_> = fields
                    .iter()
                    .map(|f| Ok((f.name, self.expr_term(f.expr)?)))
                    .collect::<Result<_, Error>>()?;

                fields.sort_by_key(|f| f.0);

                let fields = fields.into_iter().map(|f| f.1).collect();
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Constructor { adt: adt_def, variant: variant_index, fields },
                })
            }
            // TODO: If we deref a shared borrow this should be erased?
            // Can it happen?
            ExprKind::Deref { arg } => {
                if self.thir[arg].ty.is_box() || self.thir[arg].ty.ref_mutability() == Some(Not) {
                    self.expr_term(arg)
                } else {
                    Ok(Term { ty, span, kind: TermKind::Cur { term: box self.expr_term(arg)? } })
                }
            }
            ExprKind::Match { scrutinee, ref arms } => {
                let scrutinee = self.expr_term(scrutinee)?;
                let arms = arms.iter().map(|arm| self.arm_term(*arm)).collect::<Result<_, _>>()?;

                Ok(Term { ty, span, kind: TermKind::Match { scrutinee: box scrutinee, arms } })
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                let cond = self.expr_term(cond)?;
                let then = self.expr_term(then)?;
                let els = if let Some(els) = else_opt {
                    self.expr_term(els)?
                } else {
                    Term { span, ty: self.tcx.types.unit, kind: TermKind::Tuple { fields: vec![] } }
                };
                Ok(Term {
                    ty,
                    span,
                    kind: TermKind::Match {
                        scrutinee: box cond,
                        arms: vec![(Pattern::Boolean(true), then), (Pattern::Boolean(false), els)],
                    },
                })
            }
            ExprKind::Field { lhs, name, .. } => {
                let pat =
                    field_pattern(self.thir[lhs].ty, name).expect("expr_term: no term for field");

                match &self.thir[lhs].ty.kind() {
                    TyKind::Adt(def, _) => {
                        let lhs = self.expr_term(lhs)?;
                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Projection { lhs: box lhs, name, def: def.did() },
                        })
                    }
                    TyKind::Tuple(_) => {
                        let lhs = self.expr_term(lhs)?;
                        Ok(Term {
                            ty,
                            span,
                            kind: TermKind::Let {
                                pattern: pat,
                                // this is the wrong type
                                body: box Term {
                                    ty: lhs.ty,
                                    span: creusot_rustc::span::DUMMY_SP,
                                    kind: TermKind::Var(Symbol::intern("a")),
                                },
                                arg: box lhs,
                            },
                        })
                    }
                    _ => unreachable!(),
                }
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
            ExprKind::Closure { closure_id, .. } => {
                let term = typecheck(self.tcx, closure_id)?;
                // eprintln!("{term:?}");
                let pats = closure_pattern(self.tcx, closure_id)?;

                Ok(Term { ty, span, kind: TermKind::Closure { args: pats, body: box term } })
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
        match &*pat.kind {
            PatKind::Wild => Ok(Pattern::Wildcard),
            PatKind::Binding { name, .. } => Ok(Pattern::Binder(*name)),
            PatKind::Variant { subpatterns, adt_def, variant_index, .. } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| Ok((pat.field, self.pattern_term(&pat.pattern)?)))
                    .collect::<Result<_, Error>>()?;
                fields.sort_by_key(|f| f.0);

                let field_count = adt_def.variants()[*variant_index].fields.len();
                let defaults = (0usize..field_count).map(|i| (i.into(), Pattern::Wildcard));

                let fields = defaults
                    .merge_join_by(fields, |i: &(Field, _), j: &(Field, _)| i.0.cmp(&j.0))
                    .map(|el| el.reduce(|_, a| a).1)
                    .collect();

                Ok(Pattern::Constructor { adt: *adt_def, variant: *variant_index, fields })
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
                    let adt_def = pat.ty.ty_adt_def().unwrap();

                    let field_count = adt_def.variants()[0usize.into()].fields.len();
                    let defaults = (0..field_count).map(|i| (i.into(), Pattern::Wildcard));

                    let fields = defaults
                        .merge_join_by(fields, |i: &(Field, _), j: &(Field, _)| i.0.cmp(&j.0))
                        .map(|el| el.reduce(|_, a| a).1)
                        .collect();
                    Ok(Pattern::Constructor { adt: adt_def, variant: 0u32.into(), fields })
                }
            }
            PatKind::Deref { subpattern } => {
                assert!(
                    pat.ty.is_box() || pat.ty.ref_mutability() == Some(Not),
                    "pattern_term: only dereference over a box or shared reference is supported"
                );
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
                        arg: box arg,
                        body: box inner,
                    },
                })
            }
            StmtKind::Let { pattern, initializer, init_scope, .. } => {
                let pattern = self.pattern_term(pattern)?;
                if let Some(initializer) = initializer {
                    let initializer = self.expr_term(*initializer)?;
                    let span = init_scope.span(self.tcx, self.tcx.region_scope_tree(self.item_id));
                    Ok(Term {
                        ty: inner.ty,
                        span,
                        kind: TermKind::Let { pattern, arg: box initializer, body: box inner },
                    })
                } else {
                    let span =
                        self.tcx.hir().span(HirId { owner: self.item_id, local_id: init_scope.id });
                    Err(Error::new(span, "let-bindings must have values"))
                }
            }
        }
    }

    fn quant_term(&self, body: ExprId) -> Result<((Symbol, Ty<'tcx>), Term<'tcx>), Error> {
        trace!("{:?}", self.thir[body].kind);
        match self.thir[body].kind {
            ExprKind::Scope { value, .. } => self.quant_term(value),
            ExprKind::Closure { closure_id, substs, .. } => {
                let sig = match substs {
                    UpvarSubsts::Closure(subst) => subst.as_closure().sig(),
                    _ => unreachable!(),
                };

                let name = self.tcx.fn_arg_names(closure_id)[0];
                let ty = sig.input(0).skip_binder();

                Ok(((name.name, ty), typecheck(self.tcx, closure_id)?))
            }
            _ => Err(Error::new(self.thir[body].span, "unexpected error in quantifier")),
        }
    }
}

#[derive(Debug)]
pub(crate) enum Stub {
    Forall,
    Exists,
    Fin,
    Cur,
    Impl,
    Equals,
    Neq,
    VariantCheck,
    Old,
    ResultCheck,
    Absurd,
    DummyCall,
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
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("cur")) {
            return Some(Stub::Cur);
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
        if Some(*id) == tcx.get_diagnostic_item(Symbol::intern("closure_dummy_call")) {
            return Some(Stub::DummyCall);
        }
        None
    } else {
        None
    }
}

fn field_pattern(ty: Ty, field: Field) -> Option<Pattern> {
    match ty.kind() {
        TyKind::Tuple(fields) => {
            let mut fields: Vec<_> = (0..fields.len()).map(|_| Pattern::Wildcard).collect();
            fields[field.as_usize()] = Pattern::Binder(Symbol::intern("a"));

            Some(Pattern::Tuple(fields))
        }
        TyKind::Adt(ref adt, _) => {
            assert!(adt.is_struct(), "can only access fields of struct types");
            assert_eq!(adt.variants().len(), 1, "expected a single variant");
            let variant = &adt.variants()[0u32.into()];

            let mut fields: Vec<_> = (0..variant.fields.len()).map(|_| Pattern::Wildcard).collect();
            fields[field.as_usize()] = Pattern::Binder(Symbol::intern("a"));

            Some(Pattern::Constructor { adt: *adt, variant: 0usize.into(), fields })
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
        ExprKind::Closure { closure_id, .. } => !util::is_spec(tcx, closure_id.to_def_id()),
        _ => true,
    }
}

fn closure_pattern<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> CreusotResult<Vec<Pattern<'tcx>>> {
    let body_id = tcx.hir().body_owned_by(id);
    let body = tcx.hir().body(body_id);

    body.params.iter().map(|p| lower_hir_pat(tcx, p.pat)).collect()
}
use creusot_rustc::hir;

fn lower_hir_pat<'tcx>(tcx: TyCtxt<'tcx>, pat: &hir::Pat<'tcx>) -> CreusotResult<Pattern<'tcx>> {
    use creusot_rustc::hir::PatKind;
    match pat.kind {
        PatKind::Tuple(pats, _) => {
            let pats =
                pats.into_iter().map(|p| lower_hir_pat(tcx, p)).collect::<Result<Vec<_>, _>>()?;
            Ok(Pattern::Tuple(pats))
        }
        PatKind::Binding(_, _, id, _) => Ok(Pattern::Binder(id.name)),
        PatKind::Wild => Ok(Pattern::Wildcard),
        _ => Err(Error::new(pat.span, "unsupported pattern for Pearlite closure")),
    }
}

impl<'tcx> Pattern<'tcx> {
    fn binds(&self, binders: &mut HashSet<Symbol>) {
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

impl<'tcx> Term<'tcx> {
    pub(crate) fn subst(&mut self, inv_subst: &std::collections::HashMap<Symbol, Term<'tcx>>) {
        self.subst_inner(&mut HashSet::new(), inv_subst);
    }
    fn subst_inner(
        &mut self,
        bound: &HashSet<Symbol>,
        inv_subst: &std::collections::HashMap<Symbol, Term<'tcx>>,
    ) {
        match &mut self.kind {
            TermKind::Var(v) => {
                if bound.contains(v) {
                    return;
                }
                match inv_subst.get(v) {
                    Some(t) => self.kind = t.kind.clone(),
                    None => (),
                }
            }
            TermKind::Lit(_) => {}
            TermKind::Item(_, _) => {}
            TermKind::Binary { lhs, rhs, .. } => {
                lhs.subst_inner(bound, inv_subst);
                rhs.subst_inner(bound, inv_subst)
            }
            TermKind::Unary { arg, .. } => arg.subst_inner(bound, inv_subst),
            TermKind::Forall { binder, body } => {
                let mut bound = bound.clone();
                bound.insert(binder.0);

                body.subst_inner(&bound, inv_subst);
            }
            TermKind::Exists { binder, body } => {
                let mut bound = bound.clone();
                bound.insert(binder.0);

                body.subst_inner(&bound, inv_subst);
            }
            TermKind::Call { fun, args, .. } => {
                fun.subst_inner(bound, inv_subst);
                args.iter_mut().for_each(|f| f.subst_inner(bound, inv_subst))
            }
            TermKind::Constructor { fields, .. } => {
                fields.iter_mut().for_each(|f| f.subst_inner(bound, inv_subst))
            }
            TermKind::Tuple { fields } => {
                fields.iter_mut().for_each(|f| f.subst_inner(bound, inv_subst))
            }
            TermKind::Cur { term } => term.subst_inner(bound, inv_subst),
            TermKind::Fin { term } => term.subst_inner(bound, inv_subst),
            TermKind::Impl { lhs, rhs } => {
                lhs.subst_inner(bound, inv_subst);
                rhs.subst_inner(bound, inv_subst)
            }
            TermKind::Match { scrutinee, arms } => {
                scrutinee.subst_inner(bound, inv_subst);
                let mut bound = bound.clone();

                arms.iter_mut().for_each(|(pat, arm)| {
                    pat.binds(&mut bound);
                    arm.subst_inner(&bound, inv_subst)
                })
            }
            TermKind::Let { pattern, arg, body } => {
                arg.subst_inner(bound, inv_subst);
                let mut bound = bound.clone();
                pattern.binds(&mut bound);
                body.subst_inner(&bound, inv_subst);
            }
            TermKind::Projection { lhs, .. } => lhs.subst_inner(bound, inv_subst),
            TermKind::Old { term } => term.subst_inner(bound, inv_subst),
            TermKind::Closure { args, body } => {
                let mut bound = bound.clone();
                args.iter().for_each(|a| a.binds(&mut bound));
                body.subst_inner(&bound, inv_subst);
            }
            TermKind::Absurd => {}
        }
    }
}
