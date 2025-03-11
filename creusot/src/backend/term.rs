use crate::{
    backend::{
        Why3Generator,
        program::borrow_generated_id,
        ty::{constructor, floatty_to_prelude, ity_to_prelude, translate_ty, uty_to_prelude},
    },
    ctx::*,
    naming::ident_of,
    pearlite::{BinOp, Literal, Pattern, PointerKind, Term, TermKind, UnOp},
    translation::pearlite::{QuantKind, Trigger, zip_binder},
};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{EarlyBinder, Ty, TyKind};
use rustc_span::DUMMY_SP;
use rustc_type_ir::{IntTy, UintTy};
use std::iter::repeat_n;
use why3::{
    Ident,
    exp::{
        BinOp as WBinOp, Binder, Constant, Exp, Pattern as WPattern, Trigger as WTrigger,
        UnOp as WUnOp,
    },
    ty::Type,
};

pub(crate) fn lower_pure<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    term: &Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names }.lower_term(term);
    term.reassociate();
    if let Some(attr) = names.span(span) { term.with_attr(attr) } else { term }
}

pub(crate) fn lower_pat<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    pat: &Pattern<'tcx>,
) -> WPattern {
    Lower { ctx, names }.lower_pat(pat)
}

struct Lower<'a, 'tcx, N: Namer<'tcx>> {
    ctx: &'a Why3Generator<'tcx>,
    names: &'a N,
}
impl<'tcx, N: Namer<'tcx>> Lower<'_, 'tcx, N> {
    fn lower_term(&self, term: &Term<'tcx>) -> Exp {
        match &term.kind {
            TermKind::Lit(l) => lower_literal(self.ctx, self.names, l),
            TermKind::Cast { box arg } => match arg.ty.kind() {
                TyKind::Bool => {
                    let (fct_name, prelude_kind) = match term.ty.kind() {
                        TyKind::Int(ity) => ("of_bool", ity_to_prelude(self.ctx.tcx, *ity)),
                        TyKind::Uint(uty) => ("of_bool", uty_to_prelude(self.ctx.tcx, *uty)),
                        _ => self.ctx.crash_and_error(
                            DUMMY_SP,
                            "bool cast to non integral casts are currently unsupported",
                        ),
                    };

                    let qname = self.names.in_pre(prelude_kind, fct_name);
                    Exp::qvar(qname).app([self.lower_term(arg)])
                }
                TyKind::Int(_) | TyKind::Uint(_) => {
                    // to
                    let (to_fct_name, to_prelude_kind) = match arg.ty.kind() {
                        TyKind::Int(ity) => (
                            if self.names.bitwise_mode() { "to_BV256" } else { "to_int" },
                            ity_to_prelude(self.ctx.tcx, *ity),
                        ),
                        TyKind::Uint(ity) => (
                            if self.names.bitwise_mode() { "to_BV256" } else { "t'int" },
                            uty_to_prelude(self.ctx.tcx, *ity),
                        ),
                        _ => self.ctx.crash_and_error(
                            DUMMY_SP,
                            &format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    // of
                    let (of_fct_name, of_prelude_kind) = match term.ty.kind() {
                        TyKind::Int(ity) => (
                            if self.names.bitwise_mode() { "of_BV256" } else { "of_int" },
                            ity_to_prelude(self.ctx.tcx, *ity),
                        ),
                        TyKind::Uint(ity) => (
                            if self.names.bitwise_mode() { "of_BV256" } else { "of_int" },
                            uty_to_prelude(self.ctx.tcx, *ity),
                        ),
                        _ => self.ctx.crash_and_error(
                            DUMMY_SP,
                            &format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    let to_qname = self.names.in_pre(to_prelude_kind, to_fct_name);
                    let of_qname = self.names.in_pre(of_prelude_kind, of_fct_name);

                    Exp::qvar(of_qname).app([Exp::qvar(to_qname).app([self.lower_term(arg)])])
                }
                _ => self.ctx.crash_and_error(
                    DUMMY_SP,
                    "casting from a type that is not a boolean is not supported",
                ),
            },
            TermKind::Coerce { arg } => self.lower_term(arg),
            // FIXME: this is a weird dance.
            TermKind::Item(id, subst) => {
                let method = (*id, *subst);
                debug!("resolved_method={:?}", method);
                let clone = self.names.item(*id, subst);
                let item = match self.ctx.type_of(id).instantiate_identity().kind() {
                    TyKind::FnDef(_, _) => Exp::unit(),
                    _ => Exp::qvar(clone),
                };

                if matches!(self.ctx.def_kind(*id), DefKind::AssocConst) {
                    let ty = translate_ty(self.ctx, self.names, term.span, term.ty);
                    item.ascribe(ty)
                } else {
                    item
                }
            }
            TermKind::Var(v) => Exp::var(ident_of(*v)),
            TermKind::Binary { op, box lhs, box rhs } => {
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                use BinOp::*;
                match op {
                    BitAnd | BitOr | BitXor | Shl | Shr | Div | Rem => {
                        let prelude = match term.ty.kind() {
                            TyKind::Int(ity) => ity_to_prelude(self.names.tcx(), *ity),
                            TyKind::Uint(uty) => uty_to_prelude(self.names.tcx(), *uty),
                            _ => unreachable!("the operator {op:?} is only available on integer"),
                        };

                        let func_name = match (op, term.ty.kind()) {
                            (BitAnd, _) => "bw_and",
                            (BitOr, _) => "bw_or",
                            (BitXor, _) => "bw_xor",
                            (Shl, _) => "lsl_bv",
                            (Shr, TyKind::Int(_)) => "asr_bv",
                            (Shr, TyKind::Uint(_)) => "lsr_bv",
                            (Div, TyKind::Int(_)) => "sdiv",
                            (Div, TyKind::Uint(_)) => "udiv",
                            (Rem, TyKind::Int(_)) => "srem",
                            (Rem, TyKind::Uint(_)) => "urem",
                            _ => unreachable!(),
                        };

                        Exp::qvar(self.names.in_pre(prelude, func_name)).app([lhs, rhs])
                    }
                    _ => {
                        if matches!(op, Add | Sub | Mul | Le | Ge | Lt | Gt) {
                            self.names.import_prelude_module(PreMod::Int);
                        }
                        Exp::BinaryOp(binop_to_binop(*op), lhs.boxed(), rhs.boxed())
                    }
                }
            }
            TermKind::Unary { op, box arg } => {
                if matches!(op, UnOp::Neg) {
                    self.names.import_prelude_module(PreMod::Int);
                }
                let op = match op {
                    UnOp::Not => WUnOp::Not,
                    UnOp::Neg => WUnOp::Neg,
                };
                Exp::UnaryOp(op, self.lower_term(arg).boxed())
            }
            TermKind::Call { id, subst, args, .. } => Exp::qvar(self.names.item(*id, *subst))
                .app(args.into_iter().map(|arg| self.lower_term(arg))),
            TermKind::Quant { kind, binder, box body, trigger } => {
                let bound =
                    zip_binder(binder).map(|(s, t)| (s.to_string().into(), self.lower_ty(t)));
                let body = self.lower_term(body);
                let trigger = self.lower_trigger(trigger);
                match kind {
                    QuantKind::Forall => Exp::forall_trig(bound, trigger, body),
                    QuantKind::Exists => Exp::exists_trig(bound, trigger, body),
                }
            }
            TermKind::Constructor { variant, fields, .. } => {
                let TyKind::Adt(adt, subst) = term.ty.kind() else { unreachable!() };
                let fields = fields.into_iter().map(|f| self.lower_term(f)).collect();
                constructor(self.names, fields, adt.variant(*variant).def_id, subst)
            }
            TermKind::Cur { box term } => {
                assert!(term.ty.is_mutable_ptr() && term.ty.is_ref());
                self.names.import_prelude_module(PreMod::MutBor);
                self.lower_term(term).field("current".into())
            }
            TermKind::Fin { box term } => {
                self.names.import_prelude_module(PreMod::MutBor);
                self.lower_term(term).field("final".into())
            }
            TermKind::Impl { box lhs, box rhs } => {
                self.lower_term(lhs).implies(self.lower_term(rhs))
            }
            TermKind::Old { box term } => Exp::Old(self.lower_term(term).boxed()),
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
                    self.lower_term(scrutinee).match_(
                        arms.iter().map(|(pat, body)| (self.lower_pat(pat), self.lower_term(body))),
                    )
                }
            }
            TermKind::Let { pattern, box arg, box body } => Exp::Let {
                pattern: self.lower_pat(pattern),
                arg: self.lower_term(arg).boxed(),
                body: self.lower_term(body).boxed(),
            },
            TermKind::Tuple { fields } => {
                Exp::Tuple(fields.into_iter().map(|f| self.lower_term(f)).collect())
            }
            TermKind::Projection { box lhs, name } => {
                let lhs_low = self.lower_term(lhs);

                match lhs.ty.kind() {
                    TyKind::Closure(did, substs) => {
                        lhs_low.field(self.names.field(*did, substs, *name))
                    }
                    TyKind::Adt(def, substs) => {
                        lhs_low.field(self.names.field(def.did(), substs, *name))
                    }
                    TyKind::Tuple(f) => {
                        let mut fields: Box<_> = repeat_n(WPattern::Wildcard, f.len()).collect();
                        fields[name.as_usize()] = WPattern::VarP("a".into());

                        return Exp::Let {
                            pattern: WPattern::TupleP(fields),
                            arg: lhs_low.boxed(),
                            body: Exp::var("a").boxed(),
                        };
                    }
                    k => unreachable!("Projection from {k:?}"),
                }
            }
            TermKind::Closure { body, .. } => {
                let TyKind::Closure(id, subst) = term.ty.kind() else {
                    unreachable!("closure has non closure type")
                };
                let body = self.lower_term(&*body);

                let sig = self.ctx.sig(*id).clone();
                let sig = EarlyBinder::bind(sig).instantiate(self.ctx.tcx, subst);
                let binders = sig
                    .inputs
                    .iter()
                    .skip(1)
                    .map(|arg| {
                        let nm = Ident::build(&arg.0.to_string());
                        let ty = self.names.normalize(self.ctx, arg.2);
                        Binder::typed(nm, self.lower_ty(ty))
                    })
                    .collect();

                Exp::Lam(binders, body.boxed())
            }
            TermKind::Reborrow { cur, fin, inner, projection } => {
                let inner = self.lower_term(&*inner);
                let borrow_id = borrow_generated_id(self.names, inner, &projection, |x| {
                    if matches!(x.ty.kind(), TyKind::Uint(UintTy::Usize)) {
                        let qname =
                            self.names.in_pre(uty_to_prelude(self.ctx.tcx, UintTy::Usize), "t'int");
                        Exp::qvar(qname).app([self.lower_term(x)])
                    } else {
                        self.lower_term(x)
                    }
                });

                Exp::qvar(self.names.in_pre(PreMod::MutBor, "borrow_logic")).app([
                    self.lower_term(&*cur),
                    self.lower_term(&*fin),
                    borrow_id,
                ])
            }
            TermKind::Assert { .. } => Exp::unit(), // Discard cond, use unit
            TermKind::Precondition { item, args, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let mut sym = self.names.item(*item, args);
                sym.name = format!("{}'pre", &*sym.name).into();
                Exp::qvar(sym).app(params)
            }
            TermKind::Postcondition { item, args, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let mut sym = self.names.item(*item, args);
                sym.name = format!("{}'post'return'", &*sym.name).into();
                Exp::qvar(sym).app(params)
            }
        }
    }

    fn lower_pat(&self, pat: &Pattern<'tcx>) -> WPattern {
        match pat {
            Pattern::Constructor { variant, fields, substs } => {
                let fields = fields.into_iter().map(|pat| self.lower_pat(pat)).collect();
                if self.ctx.def_kind(variant) == DefKind::Variant {
                    WPattern::ConsP(self.names.constructor(*variant, *substs), fields)
                } else if fields.len() == 0 {
                    WPattern::TupleP(Box::new([]))
                } else {
                    WPattern::RecP(
                        fields
                            .into_iter()
                            .enumerate()
                            .map(|(i, f)| (self.names.field(*variant, substs, i.into()), f))
                            .filter(|(_, f)| !matches!(f, WPattern::Wildcard))
                            .collect(),
                    )
                }
            }
            Pattern::Wildcard => WPattern::Wildcard,
            Pattern::Binder(name) => WPattern::VarP(name.to_string().into()),
            Pattern::Boolean(b) => {
                if *b {
                    WPattern::mk_true()
                } else {
                    WPattern::mk_false()
                }
            }
            Pattern::Tuple(pats) => {
                WPattern::TupleP(pats.into_iter().map(|pat| self.lower_pat(pat)).collect())
            }
            Pattern::Deref { pointee, kind } => match kind {
                PointerKind::Box | PointerKind::Shr => self.lower_pat(pointee),
                PointerKind::Mut => {
                    WPattern::RecP(Box::new([("current".into(), self.lower_pat(pointee))]))
                }
            },
        }
    }

    fn lower_ty(&self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty)
    }

    fn lower_trigger(&self, triggers: &[Trigger<'tcx>]) -> Box<[WTrigger]> {
        triggers
            .iter()
            .map(|x| WTrigger(x.0.iter().map(|x| self.lower_term(x)).collect()))
            .collect()
    }
}

pub(crate) fn lower_literal<'tcx, N: Namer<'tcx>>(
    ctx: &TranslationCtx<'tcx>,
    names: &N,
    lit: &Literal<'tcx>,
) -> Exp {
    match *lit {
        Literal::Integer(i) => Constant::Int(i, None).into(),
        Literal::UInteger(i) => Constant::Uint(i, None).into(),
        Literal::MachSigned(mut i, ity) => {
            let why_ty = Type::TConstructor(names.in_pre(ity_to_prelude(ctx.tcx, ity), "t"));
            if names.bitwise_mode() {
                // In bitwise mode, integers are bit vectors, whose literals are always unsigned
                if i < 0 && ity != IntTy::I128 {
                    let target_width = ctx.tcx.sess.target.pointer_width;
                    i += 1 << ity.normalize(target_width).bit_width().unwrap();
                }
                Constant::Uint(i as u128, Some(why_ty)).into()
            } else {
                Constant::Int(i, Some(why_ty)).into()
            }
        }
        Literal::MachUnsigned(u, uty) => {
            let why_ty = Type::TConstructor(names.in_pre(uty_to_prelude(ctx.tcx, uty), "t"));
            Constant::Uint(u, Some(why_ty)).into()
        }
        Literal::Bool(true) => Constant::const_true().into(),
        Literal::Bool(false) => Constant::const_false().into(),
        Literal::Char(c) => Exp::qvar(names.in_pre(PreMod::Char, "of_int")).app([Constant::Int(
            c as u32 as i128,
            None,
        )
        .into()]),
        Literal::Function(id, subst) => {
            names.item(id, subst);
            Exp::unit()
        }
        Literal::Float(ref f, fty) => {
            let why_ty = Type::TConstructor(names.in_pre(floatty_to_prelude(fty), "t"));
            Constant::Float(f.0, Some(why_ty)).into()
        }
        Literal::ZST => Exp::unit(),
        Literal::String(ref string) => Constant::String(string.clone()).into(),
    }
}

pub(crate) fn binop_to_binop(op: BinOp) -> WBinOp {
    match op {
        BinOp::Add => WBinOp::Add,
        BinOp::Sub => WBinOp::Sub,
        BinOp::Mul => WBinOp::Mul,
        BinOp::Lt => WBinOp::Lt,
        BinOp::Le => WBinOp::Le,
        BinOp::Gt => WBinOp::Gt,
        BinOp::Ge => WBinOp::Ge,
        BinOp::Eq => WBinOp::Eq,
        BinOp::Ne => WBinOp::Ne,
        BinOp::And => WBinOp::LogAnd,
        BinOp::Or => WBinOp::LogOr,
        BinOp::BitAnd => WBinOp::BitAnd,
        BinOp::BitOr => WBinOp::BitOr,
        BinOp::BitXor => WBinOp::BitXor,
        BinOp::Shl => WBinOp::Shl,
        BinOp::Shr => WBinOp::Shr,
        BinOp::Div => todo!("Refactor binop_to_binop to support Div"),
        BinOp::Rem => todo!("Refactor binop_to_binop to support Rem"),
    }
}
