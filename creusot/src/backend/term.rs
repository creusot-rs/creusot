use super::{
    ty::{intty_to_ty, translate_ty, uintty_to_ty},
    Cloner,
};
use crate::{
    ctx::*,
    pearlite::{self, Literal, Pattern, Term, TermKind},
    util,
};
use creusot_rustc::{
    hir::{def_id::DefId, Unsafety},
    middle::ty::{subst::SubstsRef, EarlyBinder, TyCtxt},
};
use rustc_middle::ty::{Ty, TyKind};
use why3::{
    exp::{BinOp, Binder, Constant, Exp, Pattern as Pat, Purity},
    ty::Type,
    Ident, QName,
};

pub(crate) fn lower_pure<'tcx, C: Cloner<'tcx>>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut C,
    term: Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names, pure: Purity::Logic }.lower_term(term);
    term.reassociate();
    if !ctx.sess.source_map().is_imported(span) {
        term = ctx.attach_span(span, term);
    }

    term
}

pub(crate) fn lower_impure<'tcx, C: Cloner<'tcx>>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut C,
    term: Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names, pure: Purity::Program }.lower_term(term);
    term.reassociate();

    if !ctx.sess.source_map().is_imported(span) {
        term = ctx.attach_span(span, term);
    }
    term
}

pub(super) struct Lower<'a, 'tcx, C: Cloner<'tcx>> {
    pub(super) ctx: &'a mut TranslationCtx<'tcx>,
    pub(super) names: &'a mut C,
    // true when we are translating a purely logical term
    pub(super) pure: Purity,
}
impl<'tcx, C: Cloner<'tcx>> Lower<'_, 'tcx, C> {
    pub(crate) fn lower_term(&mut self, term: Term<'tcx>) -> Exp {
        match term.kind {
            TermKind::Any => Exp::Any(translate_ty(self.ctx, self.names, term.span, term.ty)),
            TermKind::Lit(l) => {
                let c = lower_literal(self.ctx, self.names, l);
                c
            }
            // FIXME: this is a weird dance.
            TermKind::Item(id, subst) => {
                let method = (id.0, subst);
                debug!("resolved_method={:?}", method);
                self.lookup_builtin(method, &mut Vec::new()).unwrap_or_else(|| {
                    // eprintln!("{id:?} {subst:?}");
                    let clone = self.names.value(id, subst);
                    match self.ctx.type_of(id.0).kind() {
                        TyKind::FnDef(_, _) => Exp::Tuple(Vec::new()),
                        _ => Exp::pure_qvar(clone),
                    }
                })
            }
            TermKind::Var(v) => Exp::pure_var(util::ident_of(v)),
            TermKind::Binary { op, box lhs, box rhs } => {
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                use pearlite::BinOp::*;

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

                        let op = if let pearlite::BinOp::Eq = op { BinOp::Eq } else { BinOp::Ne };
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
                    pearlite::UnOp::Not => why3::exp::UnOp::Not,
                    pearlite::UnOp::Neg => why3::exp::UnOp::Neg,
                };
                Exp::UnaryOp(op, box self.lower_term(arg))
            }
            TermKind::Call {
                id,
                subst,
                // fun: box Term { kind: TermKind::Item(id, subst), .. },
                args,
                ..
            } => {
                let mut args: Vec<_> = args.into_iter().map(|arg| self.lower_term(arg)).collect();

                if args.is_empty() {
                    args = vec![Exp::Tuple(vec![])];
                }

                if is_identity_from(self.ctx.tcx, id.0, subst) {
                    return args.remove(0);
                }

                self.lookup_builtin((id.0, subst), &mut args).unwrap_or_else(|| {
                    let clone = self.names.value(id, subst);
                    if self.pure == Purity::Program {
                        mk_binders(Exp::QVar(clone, self.pure), args)
                    } else {
                        Exp::Call(box Exp::QVar(clone, self.pure), args)
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
                let TyKind::Adt(_, subst) = term.ty.kind() else { unreachable!() };

                let args = fields.into_iter().map(|f| self.lower_term(f)).collect();

                let ctor = self.names.constructor(adt.did().into(), subst, variant.as_usize());
                Exp::Constructor { ctor, args }
            }
            TermKind::Cur { box term } => Exp::Current(box self.lower_term(term)),
            TermKind::Fin { box term } => Exp::Final(box self.lower_term(term)),
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
            TermKind::Projection { box lhs, name, def: did, substs } => {
                let lhs = self.lower_term(lhs);
                let accessor = match util::item_type(self.ctx.tcx, did.0) {
                    ItemType::Closure => {
                        let TyKind::Closure(did, subst) = self.ctx.type_of(did.0).kind() else { unreachable!() };
                        self.names.accessor(did.into(), subst, 0, name.as_usize())
                    }
                    _ => self.names.accessor(did, substs, 0, name.as_usize()),
                };
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
            TermKind::Reborrow { cur, fin } => Exp::Record {
                fields: vec![
                    ("current".into(), self.lower_term(*cur)),
                    ("final".into(), self.lower_term(*fin)),
                ],
            },
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
            Pattern::Constructor { def_id, variant, fields, substs } => {
                // let variant = &adt.variants()[variant];
                let fields = fields.into_iter().map(|pat| self.lower_pat(pat)).collect();
                Pat::ConsP(
                    self.names.constructor(def_id.into(), substs, variant.as_usize()),
                    fields,
                )
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

    pub(crate) fn lookup_builtin(
        &mut self,
        method: (DefId, SubstsRef<'tcx>),
        args: &mut Vec<Exp>,
    ) -> Option<Exp> {
        let def_id = method.0;
        let _substs = method.1;

        let def_id = Some(def_id);
        let builtin_attr = util::get_builtin(self.ctx.tcx, def_id.unwrap());

        if let Some(builtin) = builtin_attr.and_then(|a| QName::from_string(&a.as_str())) {
            if let Purity::Program = self.pure {
                return Some(mk_binders(
                    Exp::pure_qvar(builtin.without_search_path()),
                    args.clone(),
                ));
            } else {
                return Some(Exp::Call(
                    box Exp::pure_qvar(builtin.without_search_path()),
                    args.clone(),
                ));
            }
        }
        None
    }
}

pub(crate) fn lower_literal<'tcx, C: Cloner<'tcx>>(
    _ctx: &mut TranslationCtx<'tcx>,
    _: &mut C,
    lit: Literal<'tcx>,
) -> Exp {
    match lit {
        Literal::Integer(i) => Constant::Int(i, None).into(),
        Literal::MachSigned(u, intty) => {
            let why_ty = intty_to_ty(&intty);
            Constant::Int(u, Some(why_ty)).into()
        }
        Literal::MachUnsigned(u, uty) => {
            let why_ty = uintty_to_ty(&uty);

            Constant::Uint(u, Some(why_ty)).into()
        }
        Literal::Bool(b) => {
            if b {
                Constant::const_true().into()
            } else {
                Constant::const_false().into()
            }
        }
        Literal::Function(_, _) => Exp::Tuple(Vec::new()),
        Literal::Float(f) => Constant::Float(f).into(),
        Literal::ZST => Exp::Tuple(Vec::new()),
        Literal::String(string) => Constant::String(string).into(),
    }
}

fn binop_to_binop(op: pearlite::BinOp, purity: Purity) -> why3::exp::BinOp {
    match (op, purity) {
        (pearlite::BinOp::Add, _) => BinOp::Add,
        (pearlite::BinOp::Sub, _) => BinOp::Sub,
        (pearlite::BinOp::Mul, _) => BinOp::Mul,
        (pearlite::BinOp::Lt, _) => BinOp::Lt,
        (pearlite::BinOp::Le, _) => BinOp::Le,
        (pearlite::BinOp::Gt, _) => BinOp::Gt,
        (pearlite::BinOp::Ge, _) => BinOp::Ge,
        (pearlite::BinOp::Eq, Purity::Logic) => BinOp::Eq,
        (pearlite::BinOp::Ne, Purity::Logic) => BinOp::Ne,
        (pearlite::BinOp::And, Purity::Logic) => BinOp::LogAnd,
        (pearlite::BinOp::And, Purity::Program) => BinOp::LazyAnd,
        (pearlite::BinOp::Or, Purity::Logic) => BinOp::LogOr,
        (pearlite::BinOp::Or, Purity::Program) => BinOp::LazyOr,
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
