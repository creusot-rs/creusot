extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;

use log::*;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::thir::{
    Adt, ArmId, Block, ExprId, ExprKind, Pat, PatKind, StmtId, StmtKind, Thir,
};
use rustc_middle::ty::{AdtDef, Ty, TyKind, UpvarSubsts};
use rustc_middle::{
    mir::{BinOp, BorrowKind, Mutability::Not},
    ty::{subst::SubstsRef, Const, TyCtxt, WithOptConstParam},
};
use rustc_span::Symbol;
use rustc_target::abi::VariantIdx;

pub use rustc_middle::thir::LogicalOp;

pub use rustc_middle::mir::Field;

#[derive(Debug)]
pub enum Term<'tcx> {
    Binary { op: BinOp, lhs: Box<Term<'tcx>>, rhs: Box<Term<'tcx>> },
    Logical { op: LogicalOp, lhs: Box<Term<'tcx>>, rhs: Box<Term<'tcx>> },
    Var(String),
    Const(&'tcx Const<'tcx>),
    Forall { binder: (String, Ty<'tcx>), body: Box<Term<'tcx>> },
    Exists { binder: (String, Ty<'tcx>), body: Box<Term<'tcx>> },
    Call { id: DefId, subst: SubstsRef<'tcx>, fun: Box<Term<'tcx>>, args: Vec<Term<'tcx>> },
    Constructor { adt: &'tcx AdtDef, variant: VariantIdx, fields: Vec<Term<'tcx>> },
    Tuple { fields: Vec<Term<'tcx>> },
    Cur { term: Box<Term<'tcx>> },
    Fin { term: Box<Term<'tcx>> },
    Impl { lhs: Box<Term<'tcx>>, rhs: Box<Term<'tcx>> },
    Equals { lhs: Box<Term<'tcx>>, rhs: Box<Term<'tcx>> },
    Match { scrutinee: Box<Term<'tcx>>, arms: Vec<(Pattern<'tcx>, Term<'tcx>)> },
    Let { pattern: Pattern<'tcx>, arg: Box<Term<'tcx>>, body: Box<Term<'tcx>> },
}

#[derive(Debug)]
pub enum Pattern<'tcx> {
    Constructor { adt: &'tcx AdtDef, variant: VariantIdx, fields: Vec<Pattern<'tcx>> },
    Tuple(Vec<Pattern<'tcx>>),
    Wildcard,
    Binder(String),
    Boolean(bool),
}

pub fn typecheck<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> Term<'tcx> {
    // debug!("{:?}", id);
    let (thir, expr) = tcx.thir_body(WithOptConstParam::unknown(id));
    let thir = thir.borrow();
    lower_expr(tcx, &thir, expr).unwrap()
}

#[derive(Debug)]
struct Error {}

fn lower_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    expr: ExprId,
) -> Result<Term<'tcx>, Error> {
    trace!("{:?}", &thir[expr].kind);
    if thir.exprs.is_empty() {
        return Err(Error {});
    };
    match thir[expr].kind {
        ExprKind::Scope { value, .. } => lower_expr(tcx, thir, value),
        ExprKind::Block { body: Block { ref stmts, expr: Some(e), .. } } => {
            let mut inner = lower_expr(tcx, thir, e)?;

            for stmt in stmts.iter().rev() {
                inner = lower_stmt(tcx, thir, *stmt, inner)?;
            }

            Ok(inner)
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let lhs = lower_expr(tcx, thir, lhs)?;
            let rhs = lower_expr(tcx, thir, rhs)?;

            Ok(Term::Binary { op, lhs: box lhs, rhs: box rhs })
        }
        ExprKind::LogicalOp { op, lhs, rhs } => {
            let lhs = lower_expr(tcx, thir, lhs)?;
            let rhs = lower_expr(tcx, thir, rhs)?;

            Ok(Term::Logical { op, lhs: box lhs, rhs: box rhs })
        }

        ExprKind::VarRef { id } => {
            let map = tcx.hir();
            let name = map.name(id);
            Ok(Term::Var(name.to_string()))
        }
        // TODO: confirm this works
        ExprKind::UpvarRef { var_hir_id: id, .. } => {
            let map = tcx.hir();
            let name = map.name(id);

            Ok(Term::Var(name.to_string()))
        }
        ExprKind::Literal { literal, .. } => Ok(Term::Const(literal)),
        ExprKind::Call { ty, fun, ref args, .. } => {
            use Stub::*;
            match pearlite_stub(tcx, ty) {
                Some(Forall) => {
                    let (binder, body) = lower_quantifier(tcx, thir, args[0])?;
                    Ok(Term::Forall { binder, body: box body })
                }
                Some(Exists) => {
                    let (binder, body) = lower_quantifier(tcx, thir, args[0])?;
                    Ok(Term::Exists { binder, body: box body })
                }
                Some(Fin) => {
                    let term = lower_expr(tcx, thir, args[0])?;

                    Ok(Term::Fin { term: box term })
                }
                Some(Cur) => {
                    let term = lower_expr(tcx, thir, args[0])?;

                    Ok(Term::Cur { term: box term })
                }
                Some(Impl) => {
                    let lhs = lower_expr(tcx, thir, args[0])?;
                    let rhs = lower_expr(tcx, thir, args[1])?;

                    Ok(Term::Impl { lhs: box lhs, rhs: box rhs })
                }
                Some(Equals) => {
                    let lhs = lower_expr(tcx, thir, args[0])?;
                    let rhs = lower_expr(tcx, thir, args[1])?;

                    Ok(Term::Equals { lhs: box lhs, rhs: box rhs })
                }
                None => {
                    let fun = lower_expr(tcx, thir, fun)?;
                    let args = args
                        .iter()
                        .map(|arg| lower_expr(tcx, thir, *arg))
                        .collect::<Result<Vec<_>, _>>()?;
                    let (id, subst) = if let TyKind::FnDef(id, subst) = ty.kind() {
                        (*id, subst)
                    } else {
                        return Err(Error {});
                    };

                    Ok(Term::Call { id, subst, fun: box fun, args })
                }
            }
        }
        ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg } => lower_expr(tcx, thir, arg),
        ExprKind::Borrow { arg, .. } => {
            // Rust will introduce add unnecessary reborrows to code.
            // Since we've syntactically ruled out borrowing at a higher level, we should
            // be able erase it safely (:fingers_crossed:)
            if let ExprKind::Deref { arg } = thir[arg].kind {
                lower_expr(tcx, thir, arg)
            } else {
                Err(Error {})
            }
        }
        ExprKind::Adt(box Adt { adt_def, variant_index, ref fields, .. }) => {
            let fields =
                fields.iter().map(|f| lower_expr(tcx, thir, f.expr)).collect::<Result<_, _>>()?;
            Ok(Term::Constructor { adt: adt_def, variant: variant_index, fields })
        }
        // TODO: If we deref a shared borrow this should be erased?
        // Can it happen?
        ExprKind::Deref { arg } => {
            if thir[arg].ty.is_box() {
                lower_expr(tcx, thir, arg)
            } else if thir[arg].ty.ref_mutability() == Some(Not) {
                lower_expr(tcx, thir, arg)
            } else {
                Ok(Term::Cur { term: box lower_expr(tcx, thir, arg)? })
            }
        }
        ExprKind::Match { scrutinee, ref arms } => {
            let scrutinee = lower_expr(tcx, thir, scrutinee)?;
            let arms =
                arms.iter().map(|arm| lower_arm(tcx, thir, *arm)).collect::<Result<_, _>>()?;

            Ok(Term::Match { scrutinee: box scrutinee, arms })
        }
        ExprKind::If { cond, then, else_opt } => {
            let cond = lower_expr(tcx, thir, cond)?;
            let then = lower_expr(tcx, thir, then)?;
            if let Some(els) = else_opt {
                let els = lower_expr(tcx, thir, els)?;
                Ok(Term::Match {
                    scrutinee: box cond,
                    arms: vec![(Pattern::Boolean(true), then), (Pattern::Boolean(false), els)],
                })
            } else {
                Err(Error {})
            }
        }
        ExprKind::Field { lhs, name } => {
            let pat = field_pattern(thir[lhs].ty, name)
                .expect("lower_expr: could not make pattern for field");
            let lhs = lower_expr(tcx, thir, lhs)?;

            Ok(Term::Let { pattern: pat, arg: box lhs, body: box Term::Var("a".into()) })
        }
        ExprKind::Tuple { ref fields } => {
            let fields: Vec<_> =
                fields.iter().map(|f| lower_expr(tcx, thir, *f)).collect::<Result<_, _>>()?;
            Ok(Term::Tuple { fields })
        }
        ref ek => todo!("lower_expr: {:?}", ek),
    }
}

fn lower_arm<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    arm: ArmId,
) -> Result<(Pattern<'tcx>, Term<'tcx>), Error> {
    let arm = &thir[arm];

    if arm.guard.is_some() {
        return Err(Error {});
    }

    let pattern = lower_pattern(tcx, thir, &arm.pattern)?;
    let body = lower_expr(tcx, thir, arm.body)?;

    Ok((pattern, body))
}

fn lower_pattern<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    pat: &Pat<'tcx>,
) -> Result<Pattern<'tcx>, Error> {
    trace!("{:?}", pat);
    match &*pat.kind {
        PatKind::Wild => Ok(Pattern::Wildcard),
        PatKind::Binding { name, .. } => Ok(Pattern::Binder(name.to_string())),
        PatKind::Variant { subpatterns, adt_def, variant_index, .. } => {
            let fields: Vec<_> = subpatterns
                .iter()
                .map(|pat| lower_pattern(tcx, thir, &pat.pattern))
                .collect::<Result<_, _>>()?;

            Ok(Pattern::Constructor { adt: adt_def, variant: *variant_index, fields })
        }
        PatKind::Leaf { subpatterns } => {
            let fields: Vec<_> = subpatterns
                .iter()
                .map(|pat| lower_pattern(tcx, thir, &pat.pattern))
                .collect::<Result<_, _>>()?;

            if matches!(pat.ty.kind(), TyKind::Tuple(_)) {
                Ok(Pattern::Tuple(fields))
            } else {
                let adt_def = pat.ty.ty_adt_def().unwrap();
                Ok(Pattern::Constructor { adt: adt_def, variant: 0u32.into(), fields })
            }
        }
        PatKind::Constant { value } => {
            if !pat.ty.is_bool() {
                return Err(Error {});
            }
            Ok(Pattern::Boolean(value.val.try_to_bool().unwrap()))
        }
        _ => unimplemented!(),
        // _ => todo!(),
    }
}

fn lower_stmt<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    stmt: StmtId,
    inner: Term<'tcx>,
) -> Result<Term<'tcx>, Error> {
    match &thir[stmt].kind {
        StmtKind::Expr { .. } => todo!("expr"),
        StmtKind::Let { pattern, initializer, .. } => {
            let pattern = lower_pattern(tcx, thir, pattern)?;
            if let Some(initializer) = initializer {
                let initializer = lower_expr(tcx, thir, *initializer)?;

                Ok(Term::Let { pattern, arg: box initializer, body: box inner })
            } else {
                Err(Error {})
            }
        }
    }
}

#[derive(Debug)]
enum Stub {
    Forall,
    Exists,
    Fin,
    Cur,
    Impl,
    Equals,
}

fn pearlite_stub<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Stub> {
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
        None
    } else {
        None
    }
}

fn lower_quantifier<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    body: ExprId,
) -> Result<((String, Ty<'tcx>), Term<'tcx>), Error> {
    trace!("{:?}", thir[body].kind);
    match thir[body].kind {
        ExprKind::Scope { value, .. } => lower_quantifier(tcx, thir, value),
        ExprKind::Closure { closure_id, substs, .. } => {
            let sig = match substs {
                UpvarSubsts::Closure(subst) => subst.as_closure().sig(),
                _ => unreachable!(),
            };

            let name = tcx.fn_arg_names(closure_id)[0];
            let ty = sig.input(0).skip_binder();

            Ok(((name.to_string(), ty), typecheck(tcx, closure_id.expect_local())))
        }
        _ => Err(Error {}),
    }
}

fn field_pattern<'tcx>(ty: Ty<'tcx>, field: Field) -> Option<Pattern<'tcx>> {
    match ty.kind() {
        TyKind::Tuple(fields) => {
            let mut fields: Vec<_> = (0..fields.len()).map(|_| Pattern::Wildcard).collect();
            fields[field.as_usize()] = Pattern::Binder("a".into());

            Some(Pattern::Tuple(fields))
        }
        TyKind::Adt(_, _) => todo!(),
        _ => unreachable!("field_pattern: {:?}", ty),
    }
}
