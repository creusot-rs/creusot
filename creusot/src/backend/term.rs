use super::{program::borrow_generated_id, Why3Generator};
use crate::{
    backend::ty::{floatty_to_ty, intty_to_ty, translate_ty, uintty_to_ty},
    ctx::*,
    pearlite::{self, prusti::strip_all_refs, Literal, Pattern, Term, TermKind},
    util,
    util::get_builtin,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, Ty, TyCtxt, TyKind};
use why3::{
    exp::{BinOp, Binder, Constant, Exp, Pattern as Pat, Purity},
    ty::Type,
    Ident, QName,
};

pub(crate) fn lower_pure<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    term: &Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names, pure: Purity::Logic }.lower_term(term);
    term.reassociate();
    ctx.attach_span(span, term)
}

pub(crate) fn lower_impure<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    term: &Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names, pure: Purity::Program }.lower_term(term);
    term.reassociate();
    ctx.attach_span(span, term)
}

pub(super) struct Lower<'a, 'tcx, N: Namer<'tcx>> {
    pub(super) ctx: &'a mut Why3Generator<'tcx>,
    pub(super) names: &'a mut N,
    // true when we are translating a purely logical term
    pub(super) pure: Purity,
}
impl<'tcx, N: Namer<'tcx>> Lower<'_, 'tcx, N> {
    pub(crate) fn lower_term(&mut self, term: &Term<'tcx>) -> Exp {
        match &term.kind {
            TermKind::Lit(l) => {
                let c = lower_literal(self.ctx, self.names, l);
                c
            }
            // FIXME: this is a weird dance.
            TermKind::Item(id, subst) => {
                let method = (*id, *subst);
                debug!("resolved_method={:?}", method);
                self.lookup_builtin(method, &Vec::new()).unwrap_or_else(|| {
                    // eprintln!("{id:?} {subst:?}");
                    let clone = self.names.value(*id, subst);
                    match self.ctx.type_of(id).instantiate_identity().kind() {
                        TyKind::FnDef(_, _) => Exp::Tuple(Vec::new()),
                        _ => Exp::pure_qvar(clone),
                    }
                })
            }
            TermKind::Var(v) => Exp::pure_var(util::ident_of(*v)),
            TermKind::Binary { op, box lhs, box rhs } => {
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                use pearlite::BinOp::*;
                if matches!(op, Add | Sub | Mul | Div | Rem | Le | Ge | Lt | Gt) {
                    self.names.import_prelude_module(PreludeModule::Int);
                }

                match (op, self.pure) {
                    (Div, _) => Exp::pure_var("div".into()).app(vec![lhs, rhs]),
                    (Rem, _) => Exp::pure_var("mod".into()).app(vec![lhs, rhs]),
                    (Eq | Ne | Lt | Le | Gt | Ge, Purity::Program) => {
                        let (lfvs, rfvs) = (lhs.fvs(), rhs.fvs());
                        let mut freshvars = (0..)
                            .map(|i| format!("x{i}").into())
                            .filter(|x: &Ident| !(lfvs.contains(x) || rfvs.contains(x)));

                        let (a, lhs) = if lhs.is_pure() {
                            (lhs, None)
                        } else {
                            let v = freshvars.next().unwrap();
                            (Exp::Var(v.clone(), self.pure), Some((v, lhs)))
                        };

                        let (b, rhs) = if rhs.is_pure() {
                            (rhs, None)
                        } else {
                            let v = freshvars.next().unwrap();
                            (Exp::Var(v.clone(), self.pure), Some((v, rhs)))
                        };

                        let op = binop_to_binop(*op, Purity::Logic);
                        let mut inner =
                            Exp::Pure(Box::new(Exp::BinaryOp(op, Box::new(a), Box::new(b))));

                        if let Some((a, lhs)) = lhs {
                            inner = Exp::Let {
                                pattern: Pat::VarP(a),
                                arg: Box::new(lhs),
                                body: Box::new(inner),
                            }
                        };

                        if let Some((b, rhs)) = rhs {
                            inner = Exp::Let {
                                pattern: Pat::VarP(b),
                                arg: Box::new(rhs),
                                body: Box::new(inner),
                            }
                        };

                        inner
                    }
                    _ => {
                        Exp::BinaryOp(binop_to_binop(*op, self.pure), Box::new(lhs), Box::new(rhs))
                    }
                }
            }
            TermKind::Unary { op, box arg } => {
                let op = match op {
                    pearlite::UnOp::Not => why3::exp::UnOp::Not,
                    pearlite::UnOp::Neg => why3::exp::UnOp::Neg,
                };
                Exp::UnaryOp(op, Box::new(self.lower_term(arg)))
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

                let method = (*id, *subst);

                if is_identity_from(self.ctx.tcx, *id, method.1) {
                    return args.remove(0);
                }

                self.lookup_builtin(method, &mut args).unwrap_or_else(|| {
                    self.ctx.translate(method.0);

                    let clone = self.names.value(method.0, method.1);
                    if self.pure == Purity::Program {
                        mk_binders(Exp::QVar(clone, self.pure), args)
                    } else {
                        Exp::QVar(clone, self.pure).app(args)
                    }
                })
            }
            TermKind::Forall { binder, box body } => {
                let ty = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, binder.1);
                self.pure_exp(|this| {
                    Exp::forall(vec![(binder.0.to_string().into(), ty)], this.lower_term(body))
                })
            }
            TermKind::Exists { binder, box body } => {
                let ty = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, binder.1);
                self.pure_exp(|this| {
                    Exp::exists(vec![(binder.0.to_string().into(), ty)], this.lower_term(body))
                })
            }
            TermKind::Constructor { typ, variant, fields } => {
                self.ctx.translate(*typ);
                let TyKind::Adt(_, subst) = strip_all_refs(term.ty).kind() else { unreachable!() };
                let args = fields.into_iter().map(|f| self.lower_term(f)).collect();

                let ctor = self
                    .names
                    .constructor(self.ctx.adt_def(typ).variants()[*variant].def_id, subst);
                Exp::Constructor { ctor, args }
            }
            TermKind::Cur { box term } => {
                if strip_all_refs(term.ty).is_mutable_ptr() {
                    self.names.import_prelude_module(PreludeModule::Borrow);
                    Exp::Current(Box::new(self.lower_term(term)))
                } else {
                    self.lower_term(term)
                }
            }
            TermKind::Fin { box term } => {
                self.names.import_prelude_module(PreludeModule::Borrow);
                Exp::Final(Box::new(self.lower_term(term)))
            }
            TermKind::Impl { box lhs, box rhs } => {
                self.pure_exp(|this| this.lower_term(lhs).implies(this.lower_term(rhs)))
            }
            TermKind::Old { box term } => Exp::Old(Box::new(self.lower_term(term))),
            TermKind::Match { box scrutinee, arms } => {
                if scrutinee.ty.peel_refs().is_bool() {
                    let (true_br, false_br) = if let Pattern::Boolean(true) = arms[0].0 {
                        (&arms[0].1, &arms[1].1)
                    } else {
                        (&arms[1].1, &arms[0].1)
                    };
                    Exp::IfThenElse(
                        Box::new(self.lower_term(scrutinee)),
                        Box::new(self.lower_term(true_br)),
                        Box::new(self.lower_term(false_br)),
                    )
                } else {
                    let _ = translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, scrutinee.ty);
                    let arms = arms
                        .iter()
                        .map(|(pat, body)| (self.lower_pat(pat), self.lower_term(body)))
                        .collect();
                    Exp::Match(Box::new(self.lower_term(scrutinee)), arms)
                }
            }
            TermKind::Let { pattern, box arg, box body } => Exp::Let {
                pattern: self.lower_pat(pattern),
                arg: Box::new(self.lower_term(arg)),
                body: Box::new(self.lower_term(body)),
            },
            TermKind::Tuple { fields } => {
                Exp::Tuple(fields.into_iter().map(|f| self.lower_term(f)).collect())
            }
            TermKind::Projection { box lhs, name } => {
                let base_ty = lhs.ty;
                let lhs = self.lower_term(lhs);

                let accessor = match base_ty.kind() {
                    TyKind::Closure(did, substs) => self.names.accessor(*did, substs, 0, *name),
                    TyKind::Adt(def, substs) => {
                        self.ctx.translate_accessor(def.variants()[0u32.into()].fields[*name].did);
                        self.names.accessor(def.did(), substs, 0, *name)
                    }
                    k => unreachable!("Projection from {k:?}"),
                };

                Exp::pure_qvar(accessor).app(vec![lhs])
            }
            TermKind::Closure { body } => {
                let TyKind::Closure(id, subst) = strip_all_refs(term.ty).kind() else {
                    unreachable!("closure has non closure type")
                };
                let body = self.lower_term(&*body);

                let mut binders = Vec::new();
                let sig = self.ctx.sig(*id).clone();
                let sig = EarlyBinder::bind(sig).instantiate(self.ctx.tcx, subst);
                for arg in sig.inputs.iter().skip(1) {
                    binders
                        .push(Binder::typed(Ident::build(&arg.0.to_string()), self.lower_ty(arg.2)))
                }

                Exp::Abs(binders, Box::new(body))
            }
            TermKind::Absurd => Exp::Absurd,
            TermKind::Reborrow { cur, fin, term, projection } => {
                let inner = self.lower_term(&*term);
                let borrow_id = borrow_generated_id(inner, &projection);
                Exp::Call(
                    Box::new(Exp::QVar("Borrow.borrow_logic".into(), Purity::Logic)),
                    vec![self.lower_term(&*cur), self.lower_term(&*fin), borrow_id],
                )
            }
            TermKind::Assert { cond } => {
                let cond = self.lower_term(&*cond);
                if self.pure == Purity::Program && !cond.is_pure() {
                    Exp::Let {
                        pattern: Pat::VarP("a".into()),
                        arg: Box::new(cond),
                        body: Box::new(Exp::Assert(Box::new(Exp::impure_var("a".into())))),
                    }
                } else {
                    Exp::Assert(Box::new(cond))
                }
            }
        }
    }

    fn pure_exp(&mut self, f: impl FnOnce(&mut Self) -> Exp) -> Exp {
        match self.pure {
            Purity::Logic => f(self),
            Purity::Program => {
                self.pure = Purity::Logic;
                let ret = f(self);
                self.pure = Purity::Program;
                Exp::Pure(Box::new(ret))
            }
        }
    }

    fn lower_pat(&mut self, pat: &Pattern<'tcx>) -> Pat {
        match pat {
            Pattern::Constructor { adt, variant: _, fields, substs } => {
                // let variant = &adt.variants()[variant];
                let fields = fields.into_iter().map(|pat| self.lower_pat(pat)).collect();
                // eprintln!("{adt:?}");
                Pat::ConsP(self.names.constructor(*adt, substs), fields)
            }
            Pattern::Wildcard => Pat::Wildcard,
            Pattern::Binder(name) => Pat::VarP(name.to_string().into()),
            Pattern::Boolean(b) => {
                if *b {
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
        translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty)
    }

    pub(crate) fn lookup_builtin(
        &mut self,
        method: (DefId, GenericArgsRef<'tcx>),
        args: &Vec<Exp>,
    ) -> Option<Exp> {
        let def_id = method.0;
        let _substs = method.1;

        let def_id = Some(def_id);
        let builtin_attr = get_builtin(self.ctx.tcx, def_id.unwrap());

        if let Some(builtin) = builtin_attr.and_then(|a| QName::from_string(&a.as_str())) {
            self.names.value(def_id.unwrap(), _substs);
            // self.names.import_builtin_module(builtin.clone().module_qname());

            if let Purity::Program = self.pure {
                return Some(mk_binders(
                    Exp::pure_qvar(builtin.without_search_path()),
                    args.clone(),
                ));
            } else {
                return Some(Exp::pure_qvar(builtin.without_search_path()).app(args.clone()));
            }
        }
        None
    }
}

pub(crate) fn lower_literal<'tcx, N: Namer<'tcx>>(
    _: &mut TranslationCtx<'tcx>,
    names: &mut N,
    lit: &Literal<'tcx>,
) -> Exp {
    match &lit {
        Literal::Integer(i) => Constant::Int(*i, None).into(),
        Literal::MachSigned(u, intty) => {
            let why_ty = intty_to_ty(names, &intty);
            Constant::Int(*u, Some(why_ty)).into()
        }
        Literal::MachUnsigned(u, uty) => {
            let why_ty = uintty_to_ty(names, &uty);

            Constant::Uint(*u, Some(why_ty)).into()
        }
        Literal::Bool(b) => {
            if *b {
                Constant::const_true().into()
            } else {
                Constant::const_false().into()
            }
        }
        Literal::Function(id, subst) => {
            names.value(*id, subst);
            Exp::Tuple(Vec::new())
        }
        Literal::Float(f, fty) => {
            let why_ty = floatty_to_ty(names, &fty);
            Constant::Float(f.0, Some(why_ty)).into()
        }
        Literal::ZST => Exp::Tuple(Vec::new()),
        Literal::String(string) => Constant::String(string.clone()).into(),
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

    let call = func.app(call_args);

    impure_args.into_iter().rfold(call, |acc, arg| Exp::Let {
        pattern: Pat::VarP(arg.0.into()),
        arg: Box::new(arg.1),
        body: Box::new(acc),
    })
}

fn is_identity_from<'tcx>(tcx: TyCtxt<'tcx>, id: DefId, subst: GenericArgsRef<'tcx>) -> bool {
    if tcx.def_path_str(id) == "std::convert::From::from" && subst.len() == 1 {
        let out_ty: Ty<'tcx> = tcx.fn_sig(id).no_bound_vars().unwrap().output().skip_binder();
        return subst[0].expect_ty() == EarlyBinder::bind(out_ty).instantiate(tcx, subst);
    }
    false
}
