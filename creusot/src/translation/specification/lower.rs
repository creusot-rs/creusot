use super::typing::{LogicalOp, Pattern, Term, TermKind};
use crate::error::CreusotResult;
use crate::translation::traits::resolve_assoc_item_opt;
use crate::translation::ty::variant_accessor_name;
use crate::translation::{binop_to_binop, constant, ty::translate_ty, unop_to_unop};
use crate::util::constructor_qname;
use crate::{ctx::*, util};
use why3::mlcfg::{BinOp, Exp, Pattern as Pat, Purity};
use why3::QName;

pub fn lower_pure(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    term_id: DefId,
    term: Term<'tcx>,
) -> Exp {
    let mut term = Lower { ctx, names, pure: Purity::Logic, term_id }.lower_term(term).unwrap();
    term.reassociate();
    term
}

pub fn lower_impure(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    term_id: DefId,
    term: Term<'tcx>,
) -> Exp {
    let mut term = Lower { ctx, names, pure: Purity::Program, term_id }.lower_term(term).unwrap();
    term.reassociate();
    term
}

pub(super) struct Lower<'a, 'sess, 'tcx> {
    pub(super) ctx: &'a mut TranslationCtx<'sess, 'tcx>,
    pub(super) names: &'a mut CloneMap<'tcx>,
    // true when we are translating a purely logical term
    pub(super) pure: Purity,
    pub(super) term_id: DefId,
}

impl Lower<'_, '_, 'tcx> {
    pub fn lower_term(&mut self, term: Term<'tcx>) -> CreusotResult<Exp> {
        match term.kind {
            TermKind::Const(c) => Ok(constant::from_mir_constant_kind(
                self.ctx,
                self.names,
                c.into(),
                self.term_id,
                rustc_span::DUMMY_SP,
            )),
            TermKind::Var(v) => Ok(Exp::pure_var(util::ident_of(v))),
            TermKind::Binary { op, operand_ty, box lhs, box rhs } => {
                translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, operand_ty);

                let lhs = self.lower_term(lhs)?;
                let rhs = self.lower_term(rhs)?;

                match op {
                    rustc_middle::mir::BinOp::Div => {
                        Ok(Exp::Call(box Exp::pure_var("div".into()), vec![lhs, rhs]))
                    }
                    rustc_middle::mir::BinOp::Rem => {
                        Ok(Exp::Call(box Exp::pure_var("mod".into()), vec![lhs, rhs]))
                    }
                    _ => Ok(Exp::BinaryOp(binop_to_binop(op), box lhs, box rhs)),
                }
            }
            TermKind::Logical { op, box lhs, box rhs } => Ok(Exp::BinaryOp(
                match op {
                    LogicalOp::And => BinOp::And,
                    LogicalOp::Or => BinOp::Or,
                },
                box self.lower_term(lhs)?,
                box self.lower_term(rhs)?,
            )),
            TermKind::Unary { op, box arg } => {
                Ok(Exp::UnaryOp(unop_to_unop(op), box self.lower_term(arg)?))
            }
            TermKind::Call { id, subst, fun: box Term { kind: TermKind::Const(_), .. }, args } => {
                let mut args: Vec<_> = args.into_iter().map(|arg| self.lower_term(arg)).collect::<CreusotResult<_>>()?;

                if args.is_empty() {
                    args = vec![Exp::Tuple(vec![])];
                }

                let param_env = self.ctx.tcx.param_env(self.term_id);

                let method = resolve_assoc_item_opt(self.ctx.tcx, param_env, id, subst)
                    .unwrap_or((id, subst));
                debug!("resolved_method={:?}", method);

                if is_identity_from(self.ctx.tcx, id, method.1) {
                    return Ok(args.remove(0));
                }

                self.lookup_builtin(method, &mut args).map(Ok).unwrap_or_else(|| {
                    self.ctx.translate(method.0)?;
                    let clone = self.names.insert(method.0, method.1);
                    if self.pure == Purity::Program {
                        Ok(mk_binders(Exp::QVar(clone.qname(self.ctx.tcx, method.0), self.pure), args))
                    } else {
                        Ok(Exp::Call(
                            box Exp::QVar(clone.qname(self.ctx.tcx, method.0), self.pure),
                            args,
                        ))
                    }
                })
            }
            TermKind::Forall { binder, box body } => {
                let ty = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, binder.1);
                Ok(Exp::Forall(vec![(binder.0.into(), ty)], box self.lower_term(body)?))
            }
            TermKind::Exists { binder, box body } => {
                let ty = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, binder.1);
                Ok(Exp::Exists(vec![(binder.0.into(), ty)], box self.lower_term(body)?))
            }
            TermKind::Constructor { adt, variant, fields } => {
                self.names.import_prelude_module(PreludeModule::Type);
                let args = fields.into_iter().map(|f| self.lower_term(f)).collect::<CreusotResult<_>>()?;

                let ctor = constructor_qname(self.ctx.tcx, &adt.variants[variant]);
                crate::ty::translate_tydecl(self.ctx, rustc_span::DUMMY_SP, adt.did);
                Ok(Exp::Constructor { ctor, args })
            }
            TermKind::Cur { box term } => Ok(Exp::Current(box self.lower_term(term)?)),
            TermKind::Fin { box term } => Ok(Exp::Final(box self.lower_term(term)?)),
            TermKind::Impl { box lhs, box rhs } => {
                Ok(Exp::Impl(box self.lower_term(lhs)?, box self.lower_term(rhs)?))
            }
            TermKind::Equals { box lhs, box rhs } => {
                let lhs = self.lower_term(lhs)?;
                let rhs = self.lower_term(rhs)?;

                if let Purity::Logic = self.pure {
                    Ok(Exp::BinaryOp(BinOp::Eq, box lhs, box rhs))
                } else {
                    let (a, lhs) = if lhs.is_pure() {
                        (lhs, None)
                    } else {
                        (Exp::Var("a".into(), self.pure), Some(lhs))
                    };

                    let (b, rhs) = if rhs.is_pure() {
                        (rhs, None)
                    } else {
                        (Exp::Var("b".into(), self.pure), Some(rhs))
                    };

                    let mut inner = Exp::Pure(box Exp::BinaryOp(BinOp::Eq, box a, box b));

                    if let Some(lhs) = lhs {
                        inner = Exp::Let {
                            pattern: Pat::VarP("a".into()),
                            arg: box lhs,
                            body: box inner,
                        }
                    };

                    if let Some(rhs) = rhs {
                        inner = Exp::Let {
                            pattern: Pat::VarP("b".into()),
                            arg: box rhs,
                            body: box inner,
                        }
                    };

                    Ok(inner)
                }
            }
            TermKind::Match { box scrutinee, mut arms } => {
                if scrutinee.ty.peel_refs().is_bool() {
                    let true_br = if let Pattern::Boolean(true) = arms[0].0 {
                        arms.remove(0).1
                    } else {
                        arms.remove(1).1
                    };
                    let false_br = arms.remove(0).1;
                    Ok(Exp::IfThenElse(
                        box self.lower_term(scrutinee)?,
                        box self.lower_term(true_br)?,
                        box self.lower_term(false_br)?,
                    ))
                } else {
                    let _ = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, scrutinee.ty);
                    let arms : Vec<_> = arms
                        .into_iter()
                        .map(|arm| self.lower_arm(arm))
                        .collect::<CreusotResult<_>>()?;
                    Ok(Exp::Match(box self.lower_term(scrutinee)?, arms))
                }
            }
            TermKind::Let { pattern, box arg, box body } => Ok(Exp::Let {
                pattern: self.lower_pat(pattern),
                arg: box self.lower_term(arg)?,
                body: box self.lower_term(body)?,
            }),
            TermKind::Tuple { fields } => {
                Ok(Exp::Tuple(fields.into_iter().map(|f| self.lower_term(f)).collect::<CreusotResult<_>>()?))
            }
            TermKind::Projection { box lhs, name, def: did } => {
                let def = self.ctx.tcx.adt_def(did);
                let lhs = self.lower_term(lhs)?;
                self.ctx.translate_accessor(def.variants[0u32.into()].fields[name.as_usize()].did);
                let accessor = variant_accessor_name(
                    self.ctx.tcx,
                    did,
                    &def.variants[0u32.into()],
                    name.as_usize(),
                );
                Ok(Exp::Call(
                    box Exp::QVar(QName { module: vec!["Type".into()], name: accessor }, self.pure),
                    vec![lhs],
                ))
            }
            TermKind::Absurd => Ok(Exp::Absurd),
            t => {
                todo!("{:?}", t)
            }
        }
    }

    fn lower_arm(&mut self, arm: (Pattern<'tcx>, Term<'tcx>)) -> CreusotResult<(Pat, Exp)> {
        Ok((self.lower_pat(arm.0), self.lower_term(arm.1)?))
    }

    fn lower_pat(&mut self, pat: Pattern<'tcx>) -> Pat {
        match pat {
            Pattern::Constructor { adt, variant, fields } => {
                let variant = &adt.variants[variant];
                let fields = fields.into_iter().map(|pat| self.lower_pat(pat)).collect();
                Pat::ConsP(constructor_qname(self.ctx.tcx, variant), fields)
            }
            Pattern::Wildcard => Pat::Wildcard,
            Pattern::Binder(name) => Pat::VarP(name.into()),
            Pattern::Boolean(b) => {
                if b {
                    Pat::mk_true()
                } else {
                    Pat::mk_false()
                }
            }
            Pattern::Tuple(pats) => {
                Pat::TupleP(pats.into_iter().map(|pat| self.lower_pat(pat)).collect())
            }
        }
    }
}

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    subst::{Subst, SubstsRef},
    TyCtxt,
};

pub(super) fn mk_binders(func: Exp, args: Vec<Exp>) -> Exp {
    let mut impure_args = Vec::with_capacity(args.len());
    let mut call_args = Vec::with_capacity(args.len());
    for (nm, arg) in ('a'..).zip(args.into_iter()) {
        if arg.is_pure() {
            call_args.push(arg);
        } else {
            call_args.push(Exp::impure_var(format!("{}'", nm).into()));
            impure_args.push((format!("{}'", nm), arg));
        }
    }

    let call = Exp::Call(box func, call_args);

    impure_args.into_iter().rfold(call, |acc, arg| Exp::Let {
        pattern: Pat::VarP(arg.0.into()),
        arg: box arg.1,
        body: box acc,
    })
}

fn is_identity_from<'tcx>(tcx: TyCtxt<'tcx>, id: DefId, subst: SubstsRef<'tcx>) -> bool {
    if tcx.def_path_str(id) == "std::convert::From::from" && subst.len() == 1 {
        let out_ty = tcx.fn_sig(id).no_bound_vars().unwrap().output();
        return subst[0].expect_ty() == out_ty.subst(tcx, subst);
    }
    false
}
