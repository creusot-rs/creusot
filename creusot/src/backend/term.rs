use super::{program::borrow_generated_id, Why3Generator};
use crate::{
    backend::ty::{floatty_to_ty, intty_to_ty, translate_ty, uintty_to_ty},
    contracts_items::get_builtin,
    ctx::*,
    pearlite::{self, Literal, Pattern, PointerKind, Term, TermKind},
    translation::pearlite::{zip_binder, QuantKind, Trigger},
    util,
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, Ty, TyCtxt, TyKind};
use why3::{
    exp::{BinOp, Binder, Constant, Exp, Pattern as Pat},
    ty::Type,
    Ident, QName,
};

pub(crate) fn lower_pure<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    term: &Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names }.lower_term(term);
    term.reassociate();
    if let Some(attr) = names.span(span) {
        term.with_attr(attr)
    } else {
        term
    }
}

pub(crate) fn lower_pat<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    pat: &Pattern<'tcx>,
) -> Pat {
    Lower { ctx, names }.lower_pat(pat)
}

struct Lower<'a, 'tcx, N: Namer<'tcx>> {
    ctx: &'a mut Why3Generator<'tcx>,
    names: &'a mut N,
}
impl<'tcx, N: Namer<'tcx>> Lower<'_, 'tcx, N> {
    fn lower_term(&mut self, term: &Term<'tcx>) -> Exp {
        match &term.kind {
            TermKind::Lit(l) => lower_literal(self.ctx, self.names, l),
            // FIXME: this is a weird dance.
            TermKind::Item(id, subst) => {
                let method = (*id, *subst);
                debug!("resolved_method={:?}", method);
                let is_constant = matches!(self.ctx.def_kind(*id), DefKind::AssocConst);
                let item = self.lookup_builtin(method, &Vec::new()).unwrap_or_else(|| {
                    // eprintln!("{id:?} {subst:?}");
                    let clone = self.names.value(*id, subst);
                    match self.ctx.type_of(id).instantiate_identity().kind() {
                        TyKind::FnDef(_, _) => Exp::Tuple(Vec::new()),
                        _ => Exp::qvar(clone),
                    }
                });

                // eprintln!("{id:?} {:?} {is_constant:?}", self.ctx.def_kind(*id));
                if is_constant {
                    let ty = translate_ty(self.ctx, self.names, term.span, term.ty);
                    item.ascribe(ty)
                } else {
                    item
                }
            }
            TermKind::Var(v) => Exp::var(util::ident_of(*v)),
            TermKind::Binary { op, box lhs, box rhs } => {
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                use pearlite::BinOp::*;
                if matches!(op, Add | Sub | Mul | Div | Rem | Le | Ge | Lt | Gt) {
                    self.names.import_prelude_module(PreludeModule::Int);
                }

                match op {
                    Div => Exp::var("div").app(vec![lhs, rhs]),
                    Rem => Exp::var("mod").app(vec![lhs, rhs]),
                    _ => Exp::BinaryOp(binop_to_binop(*op), Box::new(lhs), Box::new(rhs)),
                }
            }
            TermKind::Unary { op, box arg } => {
                let op = match op {
                    pearlite::UnOp::Not => why3::exp::UnOp::Not,
                    pearlite::UnOp::Neg => why3::exp::UnOp::Neg,
                };
                Exp::UnaryOp(op, Box::new(self.lower_term(arg)))
            }
            TermKind::Call { id, subst, args, .. } => {
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
                    Exp::qvar(clone).app(args)
                })
            }
            TermKind::Quant { kind, binder, box body, trigger } => {
                let bound = zip_binder(binder)
                    .map(|(s, t)| (s.to_string().into(), self.lower_ty(t)))
                    .collect();
                let body = self.lower_term(body);
                let trigger = self.lower_trigger(trigger);
                match kind {
                    QuantKind::Forall => Exp::forall_trig(bound, trigger, body),
                    QuantKind::Exists => Exp::exists_trig(bound, trigger, body),
                }
            }
            TermKind::Constructor { typ, variant, fields } => {
                self.ctx.translate(*typ);
                let TyKind::Adt(_, subst) = term.creusot_ty().kind() else { unreachable!() };
                let args = fields.into_iter().map(|f| self.lower_term(f)).collect();

                let ctor = self
                    .names
                    .constructor(self.ctx.adt_def(typ).variants()[*variant].def_id, subst);
                Exp::Constructor { ctor, args }
            }
            TermKind::Cur { box term } => {
                if term.creusot_ty().is_mutable_ptr() {
                    self.names.import_prelude_module(PreludeModule::Borrow);
                    self.lower_term(term).field("current")
                } else {
                    self.lower_term(term)
                }
            }
            TermKind::Fin { box term } => {
                self.names.import_prelude_module(PreludeModule::Borrow);
                self.lower_term(term).field("final")
            }
            TermKind::Impl { box lhs, box rhs } => {
                self.lower_term(lhs).implies(self.lower_term(rhs))
            }
            TermKind::Old { box term } => Exp::Old(Box::new(self.lower_term(term))),
            TermKind::Match { box scrutinee, arms } => {
                if scrutinee.ty.peel_refs().is_bool() {
                    let (true_br, false_br) = if let Pattern::Boolean(true) = arms[0].0 {
                        (&arms[0].1, &arms[1].1)
                    } else {
                        (&arms[1].1, &arms[0].1)
                    };
                    Exp::if_(
                        self.lower_term(scrutinee),
                        self.lower_term(true_br),
                        self.lower_term(false_br),
                    )
                } else {
                    let _ = self.lower_ty(scrutinee.ty);
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
                    TyKind::Tuple(f) => {
                        let mut fields = vec![Pat::Wildcard; f.len()];
                        fields[name.as_usize()] = Pat::VarP("a".into());

                        return Exp::Let {
                            pattern: Pat::TupleP(fields),
                            arg: Box::new(lhs),
                            body: Box::new(Exp::var("a")),
                        };
                    }
                    k => unreachable!("Projection from {k:?}"),
                };

                Exp::qvar(accessor).app(vec![lhs])
            }
            TermKind::Closure { body } => {
                let TyKind::Closure(id, subst) = term.creusot_ty().kind() else {
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
            TermKind::Reborrow { cur, fin, inner, projection } => {
                let inner = self.lower_term(&*inner);
                let borrow_id = borrow_generated_id(inner, &projection, |x| self.lower_term(x));

                Exp::qvar("Borrow.borrow_logic".into()).app(vec![
                    self.lower_term(&*cur),
                    self.lower_term(&*fin),
                    borrow_id,
                ])
            }
            TermKind::Assert { cond } => {
                let cond = self.lower_term(&*cond);

                Exp::Assert(Box::new(cond))
            }
            TermKind::Precondition { item, args, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let mut sym = self.names.value(*item, args);
                sym.name = format!("{}'pre", &*sym.name).into();

                Exp::qvar(sym).app(params)
            }
            TermKind::Postcondition { item, args, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let mut sym = self.names.value(*item, args);
                sym.name = format!("{}'post'return'", &*sym.name).into();
                Exp::qvar(sym).app(params)
            }
            TermKind::Borrow { inner } => {
                let inner = self.lower_term(&*inner);

                Exp::qvar("Borrow.borrow_logic".into()).app(vec![
                    inner.clone(),
                    inner,
                    Exp::int(0).into(),
                ])
            }
        }
    }

    fn lower_pat(&mut self, pat: &Pattern<'tcx>) -> Pat {
        match pat {
            Pattern::Constructor { variant, fields, substs } => {
                let fields = fields.into_iter().map(|pat| self.lower_pat(pat)).collect();
                Pat::ConsP(self.names.constructor(*variant, substs), fields)
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
            Pattern::Deref { pointee, kind } => match kind {
                PointerKind::Box => self.lower_pat(pointee),
                PointerKind::Shr => self.lower_pat(pointee),
                PointerKind::Mut => Pat::RecP(vec![("current".into(), self.lower_pat(pointee))]),
            },
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

        if let Some(builtin) = builtin_attr.map(|a| QName::from_string(&a.as_str())) {
            self.names.value(def_id.unwrap(), _substs);
            // self.names.import_builtin_module(builtin.clone().module_qname());

            return Some(Exp::qvar(builtin.without_search_path()).app(args.clone()));
        }
        None
    }

    fn lower_trigger(&mut self, triggers: &[Trigger<'tcx>]) -> Vec<why3::exp::Trigger> {
        triggers
            .iter()
            .map(|x| why3::exp::Trigger(x.0.iter().map(|x| self.lower_term(x)).collect()))
            .collect()
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

pub(crate) fn binop_to_binop(op: pearlite::BinOp) -> why3::exp::BinOp {
    match op {
        pearlite::BinOp::Add => BinOp::Add,
        pearlite::BinOp::Sub => BinOp::Sub,
        pearlite::BinOp::Mul => BinOp::Mul,
        pearlite::BinOp::Lt => BinOp::Lt,
        pearlite::BinOp::Le => BinOp::Le,
        pearlite::BinOp::Gt => BinOp::Gt,
        pearlite::BinOp::Ge => BinOp::Ge,
        pearlite::BinOp::Eq => BinOp::Eq,
        pearlite::BinOp::Ne => BinOp::Ne,
        pearlite::BinOp::And => BinOp::LogAnd,
        pearlite::BinOp::Or => BinOp::LogOr,
        pearlite::BinOp::Div => todo!("Refactor binop_to_binop to support Div"),
        pearlite::BinOp::Rem => todo!("Refactor binop_to_binop to support Rem"),
    }
}

fn is_identity_from<'tcx>(tcx: TyCtxt<'tcx>, id: DefId, subst: GenericArgsRef<'tcx>) -> bool {
    if tcx.def_path_str(id) == "std::convert::From::from" && subst.len() == 1 {
        let out_ty: Ty<'tcx> = tcx.fn_sig(id).no_bound_vars().unwrap().output().skip_binder();
        return subst[0].expect_ty() == EarlyBinder::bind(out_ty).instantiate(tcx, subst);
    }
    false
}
