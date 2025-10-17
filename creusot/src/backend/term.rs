use crate::{
    backend::{
        Why3Generator,
        program::{PtrCastKind, ptr_cast_kind},
        projections::{borrow_generated_id, projections_term},
        ty::{
            constructor, floatty_to_prelude, ity_to_prelude, translate_ty, ty_to_prelude,
            uty_to_prelude,
        },
    },
    contracts_items::{is_builtin_ascription, is_new_namespace},
    ctx::*,
    naming::name,
    translation::{
        constant::valtree_to_term,
        pearlite::{
            BinOp, Literal, Pattern, PatternKind, QuantKind, Term, TermKind, Trigger, UnOp,
        },
        specification::Condition,
    },
};
use rustc_ast::Mutability;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::{DUMMY_SP, Span};
use rustc_type_ir::IntTy;
use why3::{
    Ident, Name,
    declaration::Condition as WCondition,
    exp::{
        BinOp as WBinOp, Binder, Constant, Exp, Pattern as WPattern, Trigger as WTrigger,
        UnOp as WUnOp,
    },
    ty::Type,
};

fn lower_pure_raw<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    term: &Term<'tcx>,
    weakdep: bool,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names, weakdep }.lower_term(term);
    term.reassociate();
    if let Some(attr) = names.span(span) { term.with_attr(attr) } else { term }
}

pub(crate) fn lower_pure<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    term: &Term<'tcx>,
) -> Exp {
    lower_pure_raw(ctx, names, term, false)
}

pub(crate) fn lower_pure_weakdep<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    term: &Term<'tcx>,
) -> Exp {
    lower_pure_raw(ctx, names, term, true)
}

pub(crate) fn lower_condition<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    cond: Condition<'tcx>,
) -> WCondition {
    WCondition { exp: lower_pure(ctx, names, &cond.term), expl: cond.expl }
}

pub(crate) fn unsupported_cast<'tcx>(
    ctx: &Why3Generator<'tcx>,
    span: rustc_span::Span,
    src: Ty<'tcx>,
    tgt: Ty<'tcx>,
) -> ! {
    ctx.crash_and_error(
        span,
        format!("unsupported cast from {src} to {tgt} (allowed: bool as integer, integer as integer, or pointer as pointer)"),
    )
}

struct Lower<'a, 'tcx, N: Namer<'tcx>> {
    ctx: &'a Why3Generator<'tcx>,
    names: &'a N,
    weakdep: bool,
}

impl<'tcx, N: Namer<'tcx>> Lower<'_, 'tcx, N> {
    fn lower_term(&self, term: &Term<'tcx>) -> Exp {
        match &term.kind {
            TermKind::Lit(l) => lower_literal(self.ctx, self.names, l),
            TermKind::SeqLiteral(elts) => {
                let elts: Box<[Exp]> = elts.iter().map(|elt| self.lower_term(elt)).collect();
                Exp::qvar(name::seq_create())
                    .app([Exp::int(elts.len() as i128), Exp::FunLiteral(elts)])
            }
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
                            format!("casts {:?} are currently unsupported", arg.ty.kind()),
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
                            format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    let to_qname = self.names.in_pre(to_prelude_kind, to_fct_name);
                    let of_qname = self.names.in_pre(of_prelude_kind, of_fct_name);

                    Exp::qvar(of_qname).app([Exp::qvar(to_qname).app([self.lower_term(arg)])])
                }
                // Pointer-to-pointer casts
                TyKind::RawPtr(ty1, _) if let TyKind::RawPtr(ty2, _) = term.ty.kind() => {
                    match ptr_cast_kind(self.ctx.tcx, self.names.typing_env(), ty1, ty2) {
                        PtrCastKind::Id => self.lower_term(arg),
                        PtrCastKind::Thin => {
                            let thin = self.names.in_pre(PreMod::Opaque, "thin");
                            Exp::qvar(thin).app([self.lower_term(arg)])
                        }
                        PtrCastKind::Unknown => {
                            unsupported_cast(self.ctx, term.span, arg.ty, term.ty)
                        }
                    }
                }
                _ => unsupported_cast(self.ctx, term.span, arg.ty, term.ty),
            },
            TermKind::Coerce { arg } => self.lower_term(arg),
            TermKind::Item(id, subst)
                if let TyKind::FnDef(_, _) = self.ctx.type_of(id).skip_binder().kind() =>
            {
                if !self.weakdep {
                    self.names.item(*id, subst);
                }
                Exp::unit()
            }
            TermKind::Item(id, subst) => Exp::Var(self.names.item(*id, subst)),
            TermKind::Const(c) => self.lower_term(&tyconst_to_term_final(
                *c,
                term.ty,
                self.names.source_id(),
                self.ctx,
                self.names.typing_env(),
                term.span,
            )),
            TermKind::Var(v) => Exp::var(v.0),
            TermKind::Binary { op, box lhs, box rhs } => {
                let rhs_ty = rhs.ty.kind();
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                use BinOp::*;
                if let Some(fun) = binop_function(self.names, *op, term.ty.kind()) {
                    let rhs =
                        if binop_right_int(*op) { self.names.to_int_app(rhs_ty, rhs) } else { rhs };
                    Exp::qvar(fun).app([lhs, rhs])
                } else {
                    if matches!(op, Add | Sub | Mul | Le | Ge | Lt | Gt) {
                        self.names.import_prelude_module(PreMod::Int);
                    }
                    Exp::BinaryOp(binop_to_binop(*op), lhs.boxed(), rhs.boxed())
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
            TermKind::Call { id, subst, args, .. } => {
                // Calling a function declared by `declare_namespace`: generate an identifier for it.
                if is_new_namespace(self.ctx.tcx, *id) {
                    return Exp::Constructor {
                        ctor: Name::local(self.ctx.get_namespace_constructor(*id)),
                        args: Box::new([Exp::int(0)]),
                    };
                }
                let e = Exp::Var(self.names.item(*id, subst))
                    .app(args.into_iter().map(|arg| self.lower_term(arg)));
                if is_builtin_ascription(self.ctx.tcx, *id) {
                    e.ascribe(self.lower_ty(term.ty))
                } else {
                    e
                }
            }
            TermKind::Quant { kind, binder, box body, trigger } => {
                let bound = binder.iter().map(|(s, t)| (s.0, self.lower_ty(*t)));
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
                self.lower_term(term).field(Name::Global(name::current()))
            }
            TermKind::Fin { box term } => {
                self.names.import_prelude_module(PreMod::MutBor);
                self.lower_term(term).field(Name::Global(name::final_()))
            }
            TermKind::Impl { box lhs, box rhs } => {
                self.lower_term(lhs).implies(self.lower_term(rhs))
            }
            TermKind::Old { .. } => {
                self.ctx.crash_and_error(term.span, "`old` is not allowed here")
            }
            TermKind::Match { box scrutinee, arms } => {
                // Pearlite matches are non-empty.
                if let PatternKind::Bool(b0) = arms[0].0.kind {
                    let (true_br, false_br) =
                        if b0 { (&arms[0].1, &arms[1].1) } else { (&arms[1].1, &arms[0].1) };
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
            TermKind::Let { pattern, box arg, box body } => {
                let pattern = self.lower_pat(pattern);
                let arg = self.lower_term(arg).boxed();
                let body = self.lower_term(body);
                if pattern.is_wildcard() && arg.is_unit() {
                    body
                } else {
                    Exp::Let { pattern, arg, body: body.boxed() }
                }
            }
            TermKind::Tuple { fields } if fields.is_empty() => Exp::Tuple(Box::new([])),
            TermKind::Tuple { fields } if fields.len() == 1 => self.lower_term(&fields[0]),
            TermKind::Tuple { fields } => {
                let TyKind::Tuple(tys) = term.ty.kind() else { unreachable!() };
                Exp::Record {
                    fields: fields
                        .into_iter()
                        .enumerate()
                        .map(|(ix, f)| {
                            (
                                Name::local(self.names.tuple_field(tys, ix.into())),
                                self.lower_term(f),
                            )
                        })
                        .collect(),
                }
            }
            TermKind::Projection { box lhs, idx } => {
                let lhs_low = self.lower_term(lhs);

                match lhs.ty.kind() {
                    TyKind::Closure(did, substs) => {
                        lhs_low.field(Name::local(self.names.field(*did, substs, *idx)))
                    }
                    TyKind::Adt(def, subst) => {
                        lhs_low.field(Name::local(self.names.field(def.did(), subst, *idx)))
                    }
                    TyKind::Tuple(tys) if tys.len() == 1 => lhs_low,
                    TyKind::Tuple(tys) => {
                        lhs_low.field(Name::local(self.names.tuple_field(tys, *idx)))
                    }
                    k => unreachable!("Projection from {k:?}"),
                }
            }
            TermKind::Closure { bound, body } => {
                let binders = bound
                    .iter()
                    .map(|&(ident, ty)| {
                        let ty = self.names.normalize(ty);
                        Binder::typed(ident.0, self.lower_ty(ty))
                    })
                    .collect();
                let body = self.lower_term(body);
                Exp::Lam(binders, body.boxed())
            }
            TermKind::Reborrow { inner, projections } => {
                // TODO: if inner is large, do not clone it, use a "let" instead
                let borrow_id = borrow_generated_id(
                    self.ctx,
                    self.names,
                    self.lower_term(inner),
                    term.span,
                    projections,
                    |ix: &Term<'tcx>| (self.lower_term(ix), ix.ty),
                );
                let [cur, fin] = [Term::cur, Term::fin].map(|cf| {
                    let t = projections_term(
                        self.ctx,
                        self.names.typing_env(),
                        cf((&**inner).clone()),
                        &**projections,
                        |e| e,
                        None,
                        Clone::clone,
                        term.span,
                    );
                    self.lower_term(&t)
                });

                Exp::qvar(self.names.in_pre(PreMod::MutBor, "borrow_logic"))
                    .app([cur, fin, borrow_id])
            }
            TermKind::Assert { .. } => Exp::unit(), // Discard cond, use unit
            TermKind::Precondition { item, subst, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let ident: Ident = self.names.item(*item, subst).to_ident();
                let name = Name::Local(ident, Some(why3::Symbol::intern("'pre")));
                Exp::Var(name).app(params)
            }
            TermKind::Postcondition { item, subst, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let ident: Ident = self.names.item(*item, subst).to_ident();
                let name = Name::Local(ident, Some(why3::Symbol::intern("'post'return")));
                Exp::Var(name).app(params)
            }
            TermKind::Capture(_) => unreachable!("Capture left in lowering"),
        }
    }

    // FIXME: this is a duplicate with vcgen::build_pattern_inner
    // The only difference is the `bounds` parameter
    fn lower_pat(&self, pat: &Pattern<'tcx>) -> WPattern {
        match &pat.kind {
            PatternKind::Constructor(variant, fields) => {
                let ty = self.names.normalize(pat.ty);
                let (var_did, subst) = match *ty.kind() {
                    TyKind::Adt(def, subst) => (def.variant(*variant).def_id, subst),
                    TyKind::Closure(did, subst) => (did, subst),
                    _ => unreachable!(),
                };
                let flds = fields.iter().map(|(fld, pat)| (*fld, self.lower_pat(pat)));
                if self.ctx.def_kind(var_did) == DefKind::Variant {
                    let mut pats: Box<[_]> = ty.ty_adt_def().unwrap().variants()[*variant]
                        .fields
                        .indices()
                        .map(|_| WPattern::Wildcard)
                        .collect();

                    for (idx, pat) in flds {
                        pats[idx.as_usize()] = pat
                    }
                    WPattern::ConsP(Name::local(self.names.item_ident(var_did, subst)), pats)
                } else if fields.is_empty() {
                    WPattern::TupleP(Box::new([]))
                } else {
                    let flds: Box<[_]> = flds
                        .map(|(fld, p)| (Name::local(self.names.field(var_did, subst, fld)), p))
                        .collect();
                    WPattern::RecP(flds)
                }
            }
            PatternKind::Wildcard => WPattern::Wildcard,
            PatternKind::Binder(name) => WPattern::VarP(name.0),
            PatternKind::Bool(true) => WPattern::mk_true(),
            PatternKind::Bool(false) => WPattern::mk_false(),
            PatternKind::Tuple(pats) if pats.is_empty() => WPattern::TupleP(Box::new([])),
            PatternKind::Tuple(pats) if pats.len() == 1 => self.lower_pat(&pats[0]),
            PatternKind::Tuple(pats) => {
                let ty = self.names.normalize(pat.ty);
                let TyKind::Tuple(tys) = ty.kind() else { unreachable!() };
                let flds: Box<[_]> = pats
                    .iter()
                    .enumerate()
                    .map(|(idx, pat)| {
                        (Name::local(self.names.tuple_field(tys, idx.into())), self.lower_pat(pat))
                    })
                    .filter(|(_, f)| !matches!(f, WPattern::Wildcard))
                    .collect();
                if flds.is_empty() { WPattern::Wildcard } else { WPattern::RecP(flds) }
            }
            PatternKind::Deref(pointee) => {
                let ty = self.names.normalize(pat.ty);
                match ty.kind() {
                    TyKind::Adt(def, _) if def.is_box() => self.lower_pat(pointee),
                    TyKind::Ref(_, _, Mutability::Not) => self.lower_pat(pointee),
                    TyKind::Ref(_, _, Mutability::Mut) => WPattern::RecP(Box::new([(
                        Name::Global(name::current()),
                        self.lower_pat(pointee),
                    )])),
                    _ => unreachable!(),
                }
            }
            PatternKind::Or(patterns) => {
                WPattern::OrP(patterns.iter().map(|p| self.lower_pat(p)).collect())
            }
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

impl<'a, 'tcx, N: Namer<'tcx>> HasTyCtxt<'tcx> for Lower<'a, 'tcx, N> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx()
    }
}

pub(crate) fn lower_literal<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    names: &impl Namer<'tcx>,
    lit: &Literal<'tcx>,
) -> Exp {
    match *lit {
        Literal::Integer(i) => Constant::Int(i, None).into(),
        Literal::UInteger(i) => Constant::Uint(i, None).into(),
        Literal::MachSigned(mut i, ity) => {
            let why_ty = Type::qconstructor(names.in_pre(ity_to_prelude(ctx.tcx, ity), "t"));
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
            let why_ty = Type::qconstructor(names.in_pre(uty_to_prelude(ctx.tcx, uty), "t"));
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
            let why_ty = Type::qconstructor(names.in_pre(floatty_to_prelude(fty), "t"));
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
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
            unreachable!("Bitwise operations are handled separately")
        }
    }
}

/// Return the Why3 function name of a `BinOp`, if it exists.
pub(crate) fn binop_function<'tcx>(
    namer: &impl Namer<'tcx>,
    op: BinOp,
    ty: &TyKind,
) -> Option<why3::QName> {
    use BinOp::*;
    let name = match op {
        BitAnd => "bw_and",
        BitOr => "bw_or",
        BitXor => "bw_xor",
        Shl => "lsl",
        Shr => "shr",
        _ => return None,
    };
    Some(namer.in_pre(ty_to_prelude(namer.tcx(), ty), name))
}

/// `true` if the binop expects the right operand to be cast to type `int`.
/// This is for `Shl`/`Shr` which allow left and right operands to have different types.
pub(crate) fn binop_right_int(op: BinOp) -> bool {
    use BinOp::*;
    match op {
        Shl | Shr => true,
        _ => false,
    }
}

/// Use this when we are about to output Why3 (`lower_term` here and `build_wp` in `vcgen.rs`).
/// Converts `Const::Param` to `TermKind::Item` which is ignored by `instantiate` so don't use this for terms that will be subject to substitutions
/// (in that case you probably want `Term::const_()`).
pub(crate) fn tyconst_to_term_final<'tcx>(
    c: ty::Const<'tcx>,
    ty: Ty<'tcx>,
    caller_id: DefId,
    ctx: &TranslationCtx<'tcx>,
    env: ty::TypingEnv<'tcx>,
    span: Span,
) -> Term<'tcx> {
    use rustc_type_ir::ConstKind::*;
    match c.kind() {
        Value(ty::Value { ty, valtree }) => valtree_to_term(valtree, ctx, ty, env, span),
        Unevaluated(ty::UnevaluatedConst { def, args }) => Some(Term::item(def, args, ty)),
        Param(p) => {
            let tcx = ctx.tcx;
            let def_id = tcx.generics_of(caller_id).const_param(p, tcx).def_id;
            Some(Term::item(def_id, ty::GenericArgs::empty(), ty))
        }
        _ => None,
    }
    .unwrap_or_else(|| ctx.crash_and_error(span, format!("Unsupported constant expression: {c:?}")))
}
