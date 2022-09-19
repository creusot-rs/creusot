use super::typing::{self, Literal, Pattern, Term, TermKind};
use crate::{
    ctx::*,
    translation::{
        traits::{resolve_assoc_item_opt, resolve_opt},
        ty::{intty_to_ty, translate_ty, uintty_to_ty, variant_accessor_name},
    },
    util,
    util::constructor_qname,
};
use creusot_rustc::{
    hir::Unsafety,
    middle::{
        ty,
        ty::{EarlyBinder, ParamEnv, Subst},
    },
};
use rustc_middle::ty::{Ty, TyKind};
use why3::{
    exp::{BinOp, Binder, Constant, Exp, Pattern as Pat, Purity},
    ty::Type,
    Ident,
};

pub fn lower_pure<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    // term_id: DefId,
    param_env: ParamEnv<'tcx>,
    term: Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names, pure: Purity::Logic, param_env }.lower_term(term);
    term.reassociate();
    if !ctx.sess.source_map().is_imported(span) {
        term = ctx.attach_span(span, term);
    }

    term
}

pub fn lower_impure<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    term_id: DefId,
    param_env: ParamEnv<'tcx>,

    term: Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names, pure: Purity::Program, param_env }.lower_term(term);
    term.reassociate();

    if term_id.is_local() {
        term = ctx.attach_span(span, term);
    }
    term
}

pub(super) struct Lower<'a, 'tcx> {
    pub(super) ctx: &'a mut TranslationCtx<'tcx>,
    pub(super) names: &'a mut CloneMap<'tcx>,
    // true when we are translating a purely logical term
    pub(super) pure: Purity,
    param_env: ParamEnv<'tcx>,
}
impl<'tcx> Lower<'_, 'tcx> {
    pub fn lower_term(&mut self, term: Term<'tcx>) -> Exp {
        match term.kind {
            TermKind::Lit(l) => {
                let c = lower_literal(self.ctx, self.names, l);
                c
            }
            TermKind::Item(id, subst) => {
                let method = resolve_assoc_item_opt(self.ctx.tcx, self.param_env, id, subst)
                    .unwrap_or((id, subst));
                debug!("resolved_method={:?}", method);
                self.lookup_builtin(method, &mut Vec::new()).unwrap_or_else(|| {
                    let uneval = ty::Unevaluated::new(ty::WithOptConstParam::unknown(id), subst);

                    let constant = self.ctx.tcx.mk_const(ty::ConstS {
                        kind: ty::ConstKind::Unevaluated(uneval),
                        ty: term.ty,
                    });

                    crate::constant::from_ty_const(
                        self.ctx,
                        self.names,
                        constant,
                        self.param_env,
                        creusot_rustc::span::DUMMY_SP,
                    )
                    .to_why(self.ctx, self.names, None)
                })
            }
            TermKind::Var(v) => Exp::pure_var(util::ident_of(v)),
            TermKind::Binary { op, box lhs, box rhs } => {
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                use typing::BinOp::*;
                if matches!(op, Add | Sub | Mul | Div | Rem) {
                    self.names.import_prelude_module(PreludeModule::Int);
                }

                match (op, self.pure) {
                    (Div, _) => Exp::Call(box Exp::pure_var("div".into()), vec![lhs, rhs]),
                    (Rem, _) => Exp::Call(box Exp::pure_var("mod".into()), vec![lhs, rhs]),
                    (Eq | Ne, Purity::Program) => {
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

                        let op = if let typing::BinOp::Eq = op { BinOp::Eq } else { BinOp::Ne };
                        let mut inner = Exp::Pure(box Exp::BinaryOp(op, box a, box b));

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
                    _ => Exp::BinaryOp(binop_to_binop(op, self.pure), box lhs, box rhs),
                }
            }
            TermKind::Unary { op, box arg } => {
                let op = match op {
                    typing::UnOp::Not => why3::exp::UnOp::Not,
                    typing::UnOp::Neg => why3::exp::UnOp::Neg,
                };
                Exp::UnaryOp(op, box self.lower_term(arg))
            }
            TermKind::Call {
                id,
                subst,
                // fun: box Term { kind: TermKind::Item(_, _), .. },
                args,
                ..
            } => {
                let mut args: Vec<_> = args.into_iter().map(|arg| self.lower_term(arg)).collect();

                if args.is_empty() {
                    args = vec![Exp::Tuple(vec![])];
                }

                debug!(
                    "resolved_methodb={:?}",
                    resolve_opt(self.ctx.tcx, self.param_env, id, subst)
                );
                let method =
                    resolve_opt(self.ctx.tcx, self.param_env, id, subst).unwrap_or((id, subst));
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
                let ty =
                    translate_ty(self.ctx, self.names, creusot_rustc::span::DUMMY_SP, binder.1);
                self.pure_exp(|this| {
                    Exp::Forall(vec![(binder.0.to_string().into(), ty)], box this.lower_term(body))
                })
            }
            TermKind::Exists { binder, box body } => {
                let ty =
                    translate_ty(self.ctx, self.names, creusot_rustc::span::DUMMY_SP, binder.1);
                self.pure_exp(|this| {
                    Exp::Exists(vec![(binder.0.to_string().into(), ty)], box this.lower_term(body))
                })
            }
            TermKind::Constructor { adt, variant, fields } => {
                self.ctx.translate(adt.did());
                if let TyKind::Adt(_, subst) = term.ty.kind() {
                    self.names.insert(adt.did(), subst);
                };
                let args = fields.into_iter().map(|f| self.lower_term(f)).collect();

                let ctor = constructor_qname(self.ctx, &adt.variants()[variant]);
                self.ctx.translate(adt.did());
                Exp::Constructor { ctor, args }
            }
            TermKind::Cur { box term } => {
                self.names.import_prelude_module(PreludeModule::Borrow);
                Exp::Current(box self.lower_term(term))
            }
            TermKind::Fin { box term } => {
                self.names.import_prelude_module(PreludeModule::Borrow);
                Exp::Final(box self.lower_term(term))
            }
            TermKind::Impl { box lhs, box rhs } => {
                self.pure_exp(|this| Exp::Impl(box this.lower_term(lhs), box this.lower_term(rhs)))
            }
            TermKind::Old { box term } => Exp::Old(box self.lower_term(term)),
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
                    let _ = translate_ty(
                        self.ctx,
                        self.names,
                        creusot_rustc::span::DUMMY_SP,
                        scrutinee.ty,
                    );
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
                    self.ctx,
                    did,
                    &def.variants()[0u32.into()],
                    name.as_usize(),
                );
                Exp::Call(box Exp::pure_qvar(accessor), vec![lhs])
            }
            TermKind::Closure { args, body } => {
                let mut fresh_vars = 0;

                let substs = match term.ty.kind() {
                    TyKind::Closure(_, subst) => subst,
                    _ => unreachable!("closure has non closure type!"),
                };
                let arg_tys = self
                    .ctx
                    .signature_unclosure(substs.as_closure().sig(), Unsafety::Normal)
                    .inputs();

                let mut body = self.lower_term(*body);

                let mut binders = Vec::new();

                for (arg, ty) in args.into_iter().zip(arg_tys.skip_binder().into_iter()) {
                    match arg {
                        Pattern::Binder(a) => {
                            binders.push(Binder::typed(a.to_string().into(), self.lower_ty(*ty)))
                        }
                        _ => {
                            let id = Ident::build(&format!("clos'{fresh_vars}"));
                            fresh_vars += 1;

                            body = Exp::Let {
                                pattern: self.lower_pat(arg),
                                arg: box Exp::pure_var(id.clone()),
                                body: box body,
                            };
                            binders.push(Binder::typed(id, self.lower_ty(*ty)))
                        }
                    }
                }

                Exp::Abs(binders, box body)
            }
            TermKind::Absurd => Exp::Absurd,
        }
    }

    fn pure_exp(&mut self, f: impl FnOnce(&mut Self) -> Exp) -> Exp {
        match self.pure {
            Purity::Logic => f(self),
            Purity::Program => {
                self.pure = Purity::Logic;
                let ret = f(self);
                self.pure = Purity::Program;
                Exp::Pure(box ret)
            }
        }
    }

    fn lower_pat(&mut self, pat: Pattern<'tcx>) -> Pat {
        match pat {
            Pattern::Constructor { adt, variant, fields, substs } => {
                let variant = &adt.variants()[variant];
                let fields = fields.into_iter().map(|pat| self.lower_pat(pat)).collect();
                self.names.insert(adt.did(), substs);
                Pat::ConsP(constructor_qname(self.ctx, variant), fields)
            }
            Pattern::Wildcard => Pat::Wildcard,
            Pattern::Binder(name) => Pat::VarP(name.to_string().into()),
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

    fn lower_ty(&mut self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, creusot_rustc::span::DUMMY_SP, ty)
    }
}

use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{subst::SubstsRef, TyCtxt},
};

pub fn lower_literal<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    lit: Literal,
) -> Exp {
    match lit {
        Literal::Int(u, intty) => {
            let why_ty = intty_to_ty(ctx, names, &intty);

            Constant::Int(u, Some(why_ty)).into()
        }
        Literal::Uint(u, uty) => {
            let why_ty = uintty_to_ty(ctx, names, &uty);

            Constant::Uint(u, Some(why_ty)).into()
        }
        Literal::Bool(b) => {
            if b {
                Constant::const_true().into()
            } else {
                Constant::const_false().into()
            }
        }
        Literal::Function => Exp::Tuple(Vec::new()),
        Literal::Float(f) => Constant::Float(f).into(),
        Literal::ZST => Exp::Tuple(Vec::new()),
        _ => unimplemented!("literal: {lit:?}"),
    }
}

fn binop_to_binop(op: typing::BinOp, purity: Purity) -> why3::exp::BinOp {
    match (op, purity) {
        (typing::BinOp::Add, _) => BinOp::Add,
        (typing::BinOp::Sub, _) => BinOp::Sub,
        (typing::BinOp::Mul, _) => BinOp::Mul,
        (typing::BinOp::Lt, _) => BinOp::Lt,
        (typing::BinOp::Le, _) => BinOp::Le,
        (typing::BinOp::Gt, _) => BinOp::Gt,
        (typing::BinOp::Ge, _) => BinOp::Ge,
        (typing::BinOp::Eq, Purity::Logic) => BinOp::Eq,
        (typing::BinOp::Ne, Purity::Logic) => BinOp::Ne,
        (typing::BinOp::And, Purity::Logic) => BinOp::LogAnd,
        (typing::BinOp::And, Purity::Program) => BinOp::LazyAnd,
        (typing::BinOp::Or, Purity::Logic) => BinOp::LogOr,
        (typing::BinOp::Or, Purity::Program) => BinOp::LazyOr,
        _ => unreachable!(),
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
        return subst[0].expect_ty() == EarlyBinder(out_ty).subst(tcx, subst);
    }
    false
}
