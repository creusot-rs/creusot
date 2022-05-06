use super::typing::{self, Literal, LogicalOp, Pattern, Term, TermKind};
use crate::translation::traits::resolve_assoc_item_opt;
use crate::translation::ty::translate_ty;
use crate::translation::ty::variant_accessor_name;
use crate::util::constructor_qname;
use crate::{ctx::*, util};
use rustc_middle::ty;
use rustc_middle::ty::TyKind;
use why3::mlcfg::{BinOp, Constant, Exp, Pattern as Pat, Purity};
use why3::QName;

pub fn lower_pure<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    term_id: DefId,
    term: Term<'tcx>,
) -> Exp {
    let mut term = Lower { ctx, names, pure: Purity::Logic, term_id }.lower_term(term);
    term.reassociate();
    term
}

pub fn lower_impure<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    term_id: DefId,
    term: Term<'tcx>,
) -> Exp {
    let mut term = Lower { ctx, names, pure: Purity::Program, term_id }.lower_term(term);
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
impl<'tcx> Lower<'_, '_, 'tcx> {
    pub fn lower_term(&mut self, term: Term<'tcx>) -> Exp {
        match term.kind {
            TermKind::Lit(l) => {
                let c = match l {
                    Literal::Int(u, _) => {
                        let ty = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, term.ty);

                        match term.ty.kind() {
                            TyKind::Int(_) => Constant::Int(u as i128, Some(ty)),
                            TyKind::Uint(_) => Constant::Uint(u, Some(ty)),
                            _ => unreachable!(),
                        }
                    }
                    Literal::Bool(b) => {
                        if b {
                            Constant::const_true()
                        } else {
                            Constant::const_false()
                        }
                    }
                };
                Exp::Const(c)
            }
            TermKind::Item(id, subst) => {
                let param_env = self.ctx.param_env(self.term_id);

                let method = resolve_assoc_item_opt(self.ctx.tcx, param_env, id, subst)
                    .unwrap_or((id, subst));
                debug!("resolved_method={:?}", method);
                self.lookup_builtin(method, &mut Vec::new()).unwrap_or_else(|| {
                    let uneval = ty::Unevaluated::new(ty::WithOptConstParam::unknown(id), subst);

                    let constant = self.ctx.tcx.mk_const(ty::ConstS {
                        val: ty::ConstKind::Unevaluated(uneval),
                        ty: term.ty,
                    });

                    crate::constant::from_ty_const(
                        self.ctx,
                        self.names,
                        constant,
                        param_env,
                        rustc_span::DUMMY_SP,
                    )
                })
            }
            TermKind::Var(v) => Exp::pure_var(util::ident_of(v)),
            TermKind::Binary { op, operand_ty, box lhs, box rhs } => {
                translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, operand_ty);

                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                match op {
                    typing::BinOp::Div => {
                        Exp::Call(box Exp::pure_var("div".into()), vec![lhs, rhs])
                    }
                    typing::BinOp::Rem => {
                        self.names.import_prelude_module(PreludeModule::Int);
                        Exp::Call(box Exp::pure_var("mod".into()), vec![lhs, rhs])
                    }
                    _ => Exp::BinaryOp(binop_to_binop(op), box lhs, box rhs),
                }
            }
            TermKind::Logical { op, box lhs, box rhs } => Exp::BinaryOp(
                match op {
                    LogicalOp::And => BinOp::And,
                    LogicalOp::Or => BinOp::Or,
                },
                box self.lower_term(lhs),
                box self.lower_term(rhs),
            ),
            TermKind::Unary { op, box arg } => {
                let op = match op {
                    typing::UnOp::Not => why3::mlcfg::UnOp::Not,
                    typing::UnOp::Neg => why3::mlcfg::UnOp::Neg,
                };
                Exp::UnaryOp(op, box self.lower_term(arg))
            }
            TermKind::Call {
                id,
                subst,
                fun: box Term { kind: TermKind::Item(_, _), .. },
                args,
            } => {
                let mut args: Vec<_> = args.into_iter().map(|arg| self.lower_term(arg)).collect();

                if args.is_empty() {
                    args = vec![Exp::Tuple(vec![])];
                }

                let param_env = self.ctx.param_env(self.term_id);

                let method = resolve_assoc_item_opt(self.ctx.tcx, param_env, id, subst)
                    .unwrap_or((id, subst));
                debug!("resolved_method={:?}", method);

                if is_identity_from(self.ctx.tcx, id, method.1) {
                    return args.remove(0);
                }

                self.lookup_builtin(method, &mut args).unwrap_or_else(|| {
                    self.ctx.translate(method.0);
                    let clone = self.names.insert(method.0, method.1);
                    if self.pure == Purity::Program {
                        mk_binders(Exp::QVar(clone.qname(self.ctx.tcx, method.0), self.pure), args)
                    } else {
                        Exp::Call(
                            box Exp::QVar(clone.qname(self.ctx.tcx, method.0), self.pure),
                            args,
                        )
                    }
                })
            }
            TermKind::Forall { binder, box body } => {
                let ty = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, binder.1);
                Exp::Forall(vec![(binder.0.into(), ty)], box self.lower_term(body))
            }
            TermKind::Exists { binder, box body } => {
                let ty = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, binder.1);
                Exp::Exists(vec![(binder.0.into(), ty)], box self.lower_term(body))
            }
            TermKind::Constructor { adt, variant, fields } => {
                self.names.import_prelude_module(PreludeModule::Type);
                let args = fields.into_iter().map(|f| self.lower_term(f)).collect();

                let ctor = constructor_qname(self.ctx.tcx, &adt.variants()[variant]);
                crate::ty::translate_tydecl(self.ctx, self.ctx.def_span(adt.did()), adt.did());
                Exp::Constructor { ctor, args }
            }
            TermKind::Cur { box term } => Exp::Current(box self.lower_term(term)),
            TermKind::Fin { box term } => Exp::Final(box self.lower_term(term)),
            TermKind::Impl { box lhs, box rhs } => {
                Exp::Impl(box self.lower_term(lhs), box self.lower_term(rhs))
            }
            TermKind::Old { box term } => Exp::Old(box self.lower_term(term)),
            TermKind::Equals { box lhs, box rhs } => {
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                if let Purity::Logic = self.pure {
                    Exp::BinaryOp(BinOp::Eq, box lhs, box rhs)
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

                    inner
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
                    Exp::IfThenElse(
                        box self.lower_term(scrutinee),
                        box self.lower_term(true_br),
                        box self.lower_term(false_br),
                    )
                } else {
                    let _ = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, scrutinee.ty);
                    let arms = arms
                        .into_iter()
                        .map(|(pat, body)| (self.lower_pat(pat), self.lower_term(body)))
                        .collect();
                    Exp::Match(box self.lower_term(scrutinee), arms)
                }
            }
            TermKind::Let { pattern, box arg, box body } => Exp::Let {
                pattern: self.lower_pat(pattern),
                arg: box self.lower_term(arg),
                body: box self.lower_term(body),
            },
            TermKind::Tuple { fields } => {
                Exp::Tuple(fields.into_iter().map(|f| self.lower_term(f)).collect())
            }
            TermKind::Projection { box lhs, name, def: did } => {
                let def = self.ctx.tcx.adt_def(did);
                let lhs = self.lower_term(lhs);
                self.ctx
                    .translate_accessor(def.variants()[0u32.into()].fields[name.as_usize()].did);
                let accessor = variant_accessor_name(
                    self.ctx.tcx,
                    did,
                    &def.variants()[0u32.into()],
                    name.as_usize(),
                );
                Exp::Call(
                    box Exp::QVar(QName { module: vec!["Type".into()], name: accessor }, self.pure),
                    vec![lhs],
                )
            }
            TermKind::Absurd => Exp::Absurd,
            t => {
                todo!("{:?}", t)
            }
        }
    }

    fn lower_pat(&mut self, pat: Pattern<'tcx>) -> Pat {
        match pat {
            Pattern::Constructor { adt, variant, fields } => {
                let variant = &adt.variants()[variant];
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

fn binop_to_binop(op: typing::BinOp) -> why3::mlcfg::BinOp {
    match op {
        typing::BinOp::Add => BinOp::Add,
        typing::BinOp::Sub => BinOp::Sub,
        typing::BinOp::Mul => BinOp::Mul,
        typing::BinOp::Div => BinOp::Div,
        typing::BinOp::Eq => BinOp::Eq,
        typing::BinOp::Lt => BinOp::Lt,
        typing::BinOp::Le => BinOp::Le,
        typing::BinOp::Gt => BinOp::Gt,
        typing::BinOp::Ge => BinOp::Ge,
        typing::BinOp::Ne => BinOp::Ne,
        typing::BinOp::Rem => BinOp::Mod,
    }
}

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
