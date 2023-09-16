use super::{
    clone_map::{CloneLevel, PreludeModule},
    signature::signature_of,
    term::{lower_impure, lower_pure},
    Why3Generator,
};
use crate::{
    backend::{
        closure_generic_decls, optimization, place,
        place::translate_rplace,
        ty::{self, closure_accessors, translate_closure_ty, translate_ty},
    },
    ctx::{BodyId, CloneMap, TranslationCtx},
    translation::{
        binop_to_binop,
        fmir::{self, Block, Branches, Expr, LocalDecls, Place, RValue, Statement, Terminator},
        function::{closure_contract, promoted, ClosureContract},
        unop_to_unop,
    },
    util::{self, module_name, ItemType},
};
use rustc_hir::{def::DefKind, def_id::DefId, Unsafety};
use rustc_middle::{
    mir::{BasicBlock, BinOp},
    ty::TyKind,
};
use rustc_span::DUMMY_SP;
use rustc_type_ir::{IntTy, UintTy};
use why3::{
    declaration::{self, Attribute, CfgFunction, Decl, LetDecl, LetKind, Module, Predicate, Use},
    exp::{Constant, Exp, Pattern},
    mlcfg,
    mlcfg::BlockId,
    Ident, QName,
};

use super::signature::sig_to_why3;

fn closure_ty<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Module {
    let mut names = CloneMap::new(ctx.tcx, def_id.into(), CloneLevel::Body);
    let mut decls = Vec::new();

    let TyKind::Closure(_, subst) = ctx.tcx.type_of(def_id).subst_identity().kind() else { unreachable!() };
    let env_ty = Decl::TyDecl(translate_closure_ty(ctx, &mut names, def_id, subst));

    let (clones, _) = names.to_clones(ctx);
    decls.extend(
        // Definitely a hack but good enough for the moment
        clones.into_iter().filter(|d| matches!(d, Decl::UseDecl(_))),
    );
    decls.push(env_ty);

    Module { name: format!("{}_Type", &*module_name(ctx.tcx, def_id)).into(), decls }
}

pub(crate) fn closure_type_use<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Option<Decl> {
    if !ctx.is_closure(def_id) {
        return None;
    }

    Some(Decl::UseDecl(Use {
        name: format!("{}_Type", &*module_name(ctx.tcx, def_id)).into(),
        as_: None,
        export: true,
    }))
}

pub(crate) fn closure_aux_defs<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
) -> Vec<Decl> {
    let mut decls: Vec<_> = closure_accessors(ctx, def_id)
        .into_iter()
        .map(|(sym, sig, body)| -> Decl {
            let mut sig = sig_to_why3(ctx, names, sig, def_id);
            sig.name = Ident::build(sym.as_str());

            Decl::Let(LetDecl {
                kind: Some(LetKind::Function),
                rec: false,
                ghost: false,
                sig,
                body: lower_pure(ctx, names, body),
            })
        })
        .collect();
    let contract = closure_contract(ctx, def_id).to_why(ctx, def_id, names);

    decls.extend(contract);
    decls
}

pub(crate) fn translate_closure<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (Module, Option<Module>) {
    assert!(ctx.is_closure(def_id));

    (closure_ty(ctx, def_id), translate_function(ctx, def_id))
}

impl<'tcx> ClosureContract<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        def_id: DefId,
        names: &mut CloneMap<'tcx>,
    ) -> impl Iterator<Item = Decl> {
        std::iter::once({
            let mut sig = sig_to_why3(ctx, names, self.resolve.0, def_id);
            sig.retty = None;
            sig.name = Ident::build("resolve");
            Decl::PredDecl(Predicate { sig, body: lower_pure(ctx, names, self.resolve.1) })
        })
        .chain(self.unnest.map(|(s, t)| {
            let mut sig = sig_to_why3(ctx, names, s, def_id);
            sig.retty = None;
            sig.name = Ident::build("unnest");
            Decl::PredDecl(Predicate { sig, body: lower_pure(ctx, names, t) })
        }))
        .chain(std::iter::once({
            let mut sig = sig_to_why3(ctx, names, self.precond.0, def_id);
            sig.retty = None;
            sig.name = Ident::build("precondition");

            Decl::PredDecl(Predicate { sig, body: lower_pure(ctx, names, self.precond.1) })
        }))
        .chain(self.postcond_once.map(|(s, t)| {
            let mut sig = sig_to_why3(ctx, names, s, def_id);
            sig.retty = None;
            sig.name = Ident::build("postcondition_once");
            Decl::PredDecl(Predicate { sig, body: lower_pure(ctx, names, t) })
        }))
        .chain(self.postcond_mut.map(|(s, t)| {
            let mut sig = sig_to_why3(ctx, names, s, def_id);
            sig.retty = None;
            sig.name = Ident::build("postcondition_mut");
            Decl::PredDecl(Predicate { sig, body: lower_pure(ctx, names, t) })
        }))
        .chain(self.postcond.map(|(s, t)| {
            let mut sig = sig_to_why3(ctx, names, s, def_id);
            sig.retty = None;
            sig.name = Ident::build("postcondition");
            Decl::PredDecl(Predicate { sig, body: lower_pure(ctx, names, t) })
        }))
    }
}

pub(crate) fn translate_function<'tcx, 'sess>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> Option<Module> {
    let tcx = ctx.tcx;
    let mut names = CloneMap::new(tcx, def_id.into(), CloneLevel::Body);

    let body_ids = collect_body_ids(ctx, def_id)?;
    let body = to_why(ctx, &mut names, body_ids[0]);

    let closure_defs = if ctx.tcx.is_closure(def_id) {
        closure_aux_defs(ctx, &mut names, def_id)
    } else {
        Vec::new()
    };

    let promoteds = body_ids[1..]
        .iter()
        .map(|body_id| lower_promoted(ctx, &mut names, *body_id))
        .collect::<Vec<_>>();

    let (clones, _) = names.to_clones(ctx);

    let decls = closure_generic_decls(ctx.tcx, def_id)
        .chain(closure_type_use(ctx, def_id))
        .chain(clones)
        .chain(closure_defs)
        .chain(promoteds)
        .chain(std::iter::once(body))
        .collect();

    let name = module_name(ctx.tcx, def_id);
    Some(Module { name, decls })
}

fn collect_body_ids<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> Option<Vec<BodyId>> {
    let mut ids = Vec::new();

    if def_id.is_local() && util::has_body(ctx, def_id) && !util::is_trusted(ctx.tcx, def_id) {
        ids.push(BodyId::new(def_id.expect_local(), None))
    } else {
        return None;
    }

    let promoted = ctx
        .body_with_facts(def_id.expect_local())
        .promoted
        .iter_enumerated()
        .map(|(p, p_body)| (p, p_body.return_ty()))
        .collect::<Vec<_>>();

    ids.extend(promoted.iter().filter_map(|(p, p_ty)| {
        if util::ghost_closure_id(ctx.tcx, *p_ty).is_none() {
            Some(BodyId::new(def_id.expect_local(), Some(*p)))
        } else {
            None
        }
    }));

    Some(ids)
}

// According to @oli-obk, promoted bodies are:
// > it's completely linear, not even conditions or asserts inside. we should probably document all that with validation
// On this supposition we can simplify the translation *dramatically* and produce why3 constants
// instead of cfgs
//
// We use a custom translation because if we use `any` inside a `constant` / `function` its body is marked as opaque, and `mlcfg` heavily uses `any`.
fn lower_promoted<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    body_id: BodyId,
) -> Decl {
    let promoted = promoted::translate_promoted(ctx, body_id);
    let (sig, fmir) = promoted.unwrap_or_else(|e| e.emit(ctx.tcx.sess));

    let mut sig = sig_to_why3(ctx, names, sig, body_id.def_id());
    sig.name = format!("promoted{:?}", body_id.promoted.unwrap().as_usize()).into();

    let mut previous_block = None;
    let mut exp = Exp::impure_var("_0".into());
    for (id, bbd) in fmir.blocks.into_iter().rev() {
        // Safety check
        match bbd.terminator {
            fmir::Terminator::Goto(prev) => {
                assert!(previous_block == Some(prev))
            }
            fmir::Terminator::Return => {
                assert!(previous_block == None);
            }
            _ => {}
        };

        previous_block = Some(id);

        // FIXME
        let exps: Vec<_> =
            bbd.stmts.into_iter().map(|s| s.to_why(ctx, names, &fmir.locals)).flatten().collect();
        exp = exps.into_iter().rfold(exp, |acc, asgn| match asgn {
            why3::mlcfg::Statement::Assign { lhs, rhs } => {
                Exp::Let { pattern: Pattern::VarP(lhs), arg: Box::new(rhs), body: Box::new(acc) }
            }
            why3::mlcfg::Statement::Assume(_) => acc,
            why3::mlcfg::Statement::Invariant(_)
            | why3::mlcfg::Statement::Variant(_)
            | why3::mlcfg::Statement::Assert(_) => {
                ctx.crash_and_error(ctx.def_span(body_id.def_id()), "unsupported promoted constant")
            }
        });
    }

    Decl::Let(LetDecl { sig, rec: false, kind: Some(LetKind::Constant), body: exp, ghost: false })
}

pub fn to_why<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    body_id: BodyId,
) -> Decl {
    let mut body = ctx.fmir_body(body_id).unwrap().clone();

    let usage = optimization::gather_usage(&body);
    optimization::simplify_fmir(usage, &mut body);

    let blocks = body
        .blocks
        .into_iter()
        .map(|(bb, bbd)| (BlockId(bb.into()), bbd.to_why(ctx, names, &body.locals)))
        .collect();

    let vars: Vec<_> = body
        .locals
        .into_iter()
        .map(|(id, decl)| {
            let init =
                if decl.arg { Some(Exp::impure_var(Ident::build(id.as_str()))) } else { None };
            (
                false,
                Ident::build(id.as_str()),
                ty::translate_ty(ctx, names, decl.span, decl.ty),
                init,
            )
        })
        .collect();

    let entry =
        mlcfg::Block { statements: Vec::new(), terminator: mlcfg::Terminator::Goto(BlockId(0)) };

    let mut sig = signature_of(ctx, names, body_id.def_id());
    if matches!(util::item_type(ctx.tcx, body_id.def_id()), ItemType::Program | ItemType::Closure) {
        sig.attrs.push(declaration::Attribute::Attr("cfg:stackify".into()));
        sig.attrs.push(declaration::Attribute::Attr("cfg:subregion_analysis".into()));
    };

    Decl::CfgDecl(CfgFunction { sig, rec: true, constant: false, entry, blocks, vars })
}

impl<'tcx> Expr<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
    ) -> Exp {
        match self {
            Expr::Move(pl) => {
                // TODO invalidate original place
                pl.as_rplace(ctx, names, locals)
            }
            Expr::Copy(pl) => pl.as_rplace(ctx, names, locals),
            Expr::BinOp(BinOp::BitAnd, ty, l, r) if ty.is_bool() => {
                l.to_why(ctx, names, locals).lazy_and(r.to_why(ctx, names, locals))
            }
            Expr::BinOp(BinOp::Eq, ty, l, r) if ty.is_bool() => {
                names.import_prelude_module(PreludeModule::Bool);
                Exp::impure_qvar(QName::from_string("Bool.eqb").unwrap())
                    .app(vec![l.to_why(ctx, names, locals), r.to_why(ctx, names, locals)])
            }
            Expr::BinOp(BinOp::Ne, ty, l, r) if ty.is_bool() => {
                names.import_prelude_module(PreludeModule::Bool);
                Exp::impure_qvar(QName::from_string("Bool.neqb").unwrap())
                    .app(vec![l.to_why(ctx, names, locals), r.to_why(ctx, names, locals)])
            }
            Expr::BinOp(op, ty, l, r) => {
                // Hack
                translate_ty(ctx, names, DUMMY_SP, ty);

                Exp::BinaryOp(
                    binop_to_binop(ctx, ty, op),
                    Box::new(l.to_why(ctx, names, locals)),
                    Box::new(r.to_why(ctx, names, locals)),
                )
            }
            Expr::UnaryOp(op, ty, arg) => {
                Exp::UnaryOp(unop_to_unop(ty, op), Box::new(arg.to_why(ctx, names, locals)))
            }
            Expr::Constructor(id, subst, args) => {
                let args = args.into_iter().map(|a| a.to_why(ctx, names, locals)).collect();

                match ctx.def_kind(id) {
                    DefKind::Closure => {
                        let ctor = names.constructor(id, subst);
                        Exp::Constructor { ctor, args }
                    }
                    _ => {
                        let ctor = names.constructor(id, subst);
                        Exp::Constructor { ctor, args }
                    }
                }
            }
            Expr::Call(id, subst, args) => {
                let mut args: Vec<_> =
                    args.into_iter().map(|a| a.to_why(ctx, names, locals)).collect();
                let fname = names.value(id, subst);

                let exp = if ctx.is_closure(id) {
                    assert!(args.len() == 2, "closures should only have two arguments (env, args)");

                    let real_sig =
                        ctx.signature_unclosure(subst.as_closure().sig(), Unsafety::Normal);
                    let closure_arg_count = real_sig.inputs().skip_binder().len();
                    let names = ('a'..).take(closure_arg_count);

                    let mut closure_args = vec![args.remove(0)];

                    closure_args
                        .extend(names.clone().map(|nm| Exp::impure_var(nm.to_string().into())));

                    Exp::Let {
                        pattern: Pattern::TupleP(
                            names.map(|nm| Pattern::VarP(nm.to_string().into())).collect(),
                        ),
                        arg: Box::new(args.remove(0)),
                        body: Box::new(Exp::impure_qvar(fname).app(closure_args)),
                    }
                } else {
                    Exp::impure_qvar(fname).app(args)
                };
                exp
            }
            Expr::Constant(c) => lower_impure(ctx, names, c),
            Expr::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(ctx, names, locals)).collect())
            }
            Expr::Span(sp, e) => {
                let e = e.to_why(ctx, names, locals);
                ctx.attach_span(sp, e)
            } // Expr::Cast(_, _) => todo!(),
            Expr::Cast(e, source, target) => {
                let to_int = match source.kind() {
                    TyKind::Int(ity) => {
                        names.import_prelude_module(int_to_prelude(*ity));
                        int_to_int(ity)
                    }
                    TyKind::Uint(uty) => {
                        names.import_prelude_module(uint_to_prelude(*uty));
                        uint_to_int(uty)
                    }
                    TyKind::Bool => {
                        names.import_prelude_module(PreludeModule::Bool);
                        Exp::impure_qvar(QName::from_string("Bool.to_int").unwrap())
                    }
                    _ => ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                let from_int = match target.kind() {
                    TyKind::Int(ity) => int_from_int(ity),
                    TyKind::Uint(uty) => uint_from_int(uty),
                    TyKind::Char => {
                        names.import_prelude_module(PreludeModule::Char);
                        Exp::impure_qvar(QName::from_string("Char.chr").unwrap())
                    }
                    _ => ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                from_int.app_to(to_int.app_to(e.to_why(ctx, names, locals)))
            }
            Expr::Len(pl) => {
                let len_call = Exp::impure_qvar(QName::from_string("Slice.length").unwrap())
                    .app_to(pl.to_why(ctx, names, locals));
                len_call
            }
            Expr::Array(fields) => Exp::impure_qvar(QName::from_string("Slice.create").unwrap())
                .app_to(Exp::Const(Constant::Int(fields.len() as i128, None)))
                .app_to(Exp::Sequence(
                    fields.into_iter().map(|f| f.to_why(ctx, names, locals)).collect(),
                )),
            Expr::Repeat(e, len) => Exp::impure_qvar(QName::from_string("Slice.create").unwrap())
                .app_to(len.to_why(ctx, names, locals))
                .app_to(Exp::FnLit(Box::new(e.to_why(ctx, names, locals)))),
        }
    }

    fn invalidated_places(&self, places: &mut Vec<fmir::Place<'tcx>>) {
        match self {
            Expr::Move(p) => places.push(p.clone()),
            Expr::Copy(_) => {}
            Expr::BinOp(_, _, l, r) => {
                l.invalidated_places(places);
                r.invalidated_places(places)
            }
            Expr::UnaryOp(_, _, e) => e.invalidated_places(places),
            Expr::Constructor(_, _, es) => es.iter().for_each(|e| e.invalidated_places(places)),
            Expr::Call(_, _, es) => es.iter().for_each(|e| e.invalidated_places(places)),
            Expr::Constant(_) => {}
            Expr::Cast(e, _, _) => e.invalidated_places(places),
            Expr::Tuple(es) => es.iter().for_each(|e| e.invalidated_places(places)),
            Expr::Span(_, e) => e.invalidated_places(places),
            Expr::Len(e) => e.invalidated_places(places),
            Expr::Array(f) => f.iter().for_each(|f| f.invalidated_places(places)),
            Expr::Repeat(e, len) => {
                e.invalidated_places(places);
                len.invalidated_places(places)
            }
        }
    }
}

impl<'tcx> Terminator<'tcx> {
    pub(crate) fn retarget(&mut self, from: BasicBlock, to: BasicBlock) {
        match self {
            Terminator::Goto(bb) => {
                if *bb == from {
                    *bb = to
                };
            }
            Terminator::Switch(_, brs) => match brs {
                Branches::Int(brs, def) => {
                    if *def == from {
                        *def = to
                    };
                    for (_, bb) in brs {
                        if *bb == from {
                            *bb = from
                        }
                    }
                }
                Branches::Uint(brs, def) => {
                    if *def == from {
                        *def = to
                    };
                    for (_, bb) in brs {
                        if *bb == from {
                            *bb = from
                        }
                    }
                }
                Branches::Constructor(_, _, brs, def) => {
                    if *def == from {
                        *def = to
                    };
                    for (_, bb) in brs {
                        if *bb == from {
                            *bb = from
                        }
                    }
                }
                Branches::Bool(bb1, bb2) => {
                    if *bb1 == from {
                        *bb1 = to
                    };
                    if *bb2 == from {
                        *bb2 = to;
                    }
                }
            },
            Terminator::Return => {}
            Terminator::Abort => {}
        }
    }

    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
    ) -> why3::mlcfg::Terminator {
        use why3::mlcfg::Terminator::*;
        match self {
            Terminator::Goto(bb) => Goto(BlockId(bb.into())),
            Terminator::Switch(switch, branches) => {
                let discr = switch.to_why(ctx, names, locals);
                branches.to_why(ctx, names, discr)
            }
            Terminator::Return => Return,
            Terminator::Abort => Absurd,
        }
    }
}

impl<'tcx> Branches<'tcx> {
    fn to_why(
        self,
        _ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        discr: Exp,
    ) -> mlcfg::Terminator {
        use why3::mlcfg::Terminator::*;

        match self {
            Branches::Int(brs, def) => {
                brs.into_iter().rfold(Goto(BlockId(def.into())), |acc, (val, bb)| {
                    Switch(
                        discr.clone().eq(Exp::Const(why3::exp::Constant::Int(val, None))),
                        vec![
                            (Pattern::mk_true(), Goto(BlockId(bb.into()))),
                            (Pattern::mk_false(), acc),
                        ],
                    )
                })
            }
            Branches::Uint(brs, def) => {
                brs.into_iter().rfold(Goto(BlockId(def.into())), |acc, (val, bb)| {
                    Switch(
                        discr.clone().eq(Exp::Const(why3::exp::Constant::Uint(val, None))),
                        vec![
                            (Pattern::mk_true(), Goto(BlockId(bb.into()))),
                            (Pattern::mk_false(), acc),
                        ],
                    )
                })
            }
            Branches::Constructor(adt, substs, vars, def) => {
                let count = adt.variants().len();
                let brs = vars
                    .into_iter()
                    .map(|(var, bb)| {
                        let variant = &adt.variant(var);
                        let wilds = variant.fields.iter().map(|_| Pattern::Wildcard).collect();
                        let cons_name = names.constructor(variant.def_id, substs);
                        (Pattern::ConsP(cons_name, wilds), Goto(BlockId(bb.into())))
                    })
                    .chain(std::iter::once((Pattern::Wildcard, Goto(BlockId(def.into())))))
                    .take(count);

                Switch(discr, brs.collect())
            }
            Branches::Bool(f, t) => Switch(
                discr,
                vec![
                    (Pattern::mk_false(), Goto(BlockId(f.into()))),
                    (Pattern::mk_true(), Goto(BlockId(t.into()))),
                ],
            ),
        }
    }
}

impl<'tcx> Block<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
    ) -> why3::mlcfg::Block {
        mlcfg::Block {
            statements: self.stmts.into_iter().flat_map(|s| s.to_why(ctx, names, locals)).collect(),
            terminator: self.terminator.to_why(ctx, names, locals),
        }
    }
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn as_rplace(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
    ) -> why3::Exp {
        translate_rplace(ctx, names, locals, self.local, &self.projection)
    }
}

impl<'tcx> Statement<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
    ) -> Vec<mlcfg::Statement> {
        match self {
            Statement::Assignment(lhs, RValue::Borrow(rhs)) => {
                let borrow = Exp::Call(
                    Box::new(Exp::impure_qvar(QName::from_string("Borrow.borrow_mut").unwrap())),
                    vec![rhs.as_rplace(ctx, names, locals)],
                );
                let reassign = Exp::Final(Box::new(lhs.as_rplace(ctx, names, locals)));

                vec![
                    place::create_assign_inner(ctx, names, locals, &lhs, borrow),
                    place::create_assign_inner(ctx, names, locals, &rhs, reassign),
                ]
            }
            Statement::Assignment(lhs, RValue::Ghost(rhs)) => {
                let ghost = lower_pure(ctx, names, rhs);

                vec![place::create_assign_inner(ctx, names, locals, &lhs, ghost)]
            }
            Statement::Assignment(lhs, RValue::Expr(rhs)) => {
                let mut invalid = Vec::new();
                rhs.invalidated_places(&mut invalid);
                let rhs = rhs.to_why(ctx, names, locals);
                let mut exps = vec![place::create_assign_inner(ctx, names, locals, &lhs, rhs)];
                for pl in invalid {
                    let ty = pl.ty(ctx.tcx, locals);
                    let ty = translate_ty(ctx, names, DUMMY_SP, ty);
                    exps.push(place::create_assign_inner(ctx, names, locals, &pl, Exp::Any(ty)));
                }
                exps
            }
            Statement::Resolve(id, subst, pl) => {
                ctx.translate(id);

                let rp = Exp::impure_qvar(names.value(id, subst));

                let assume = rp.app_to(pl.as_rplace(ctx, names, locals));
                vec![mlcfg::Statement::Assume(assume)]
            }
            Statement::Assertion { cond, msg } => {
                vec![mlcfg::Statement::Assert(Exp::Attr(
                    Attribute::Attr(format!("expl:{msg}")),
                    Box::new(lower_pure(ctx, names, cond)),
                ))]
            }

            Statement::Invariant(inv) => {
                vec![mlcfg::Statement::Invariant(lower_pure(ctx, names, inv))]
            }
            Statement::Variant(var) => vec![mlcfg::Statement::Variant(lower_pure(ctx, names, var))],
            Statement::AssumeTyInv(ty, pl) => {
                let inv_fun = Exp::impure_qvar(names.ty_inv(ty));
                let arg = Exp::Final(Box::new(pl.as_rplace(ctx, names, locals)));

                vec![mlcfg::Statement::Assume(inv_fun.app_to(arg))]
            }
            Statement::AssertTyInv(ty, pl) => {
                let inv_fun = Exp::impure_qvar(names.ty_inv(ty));
                let arg = pl.as_rplace(ctx, names, locals);
                let exp = Exp::Attr(
                    Attribute::Attr(format!("expl:type invariant")),
                    Box::new(inv_fun.app_to(arg)),
                );

                vec![mlcfg::Statement::Assert(exp)]
            }
        }
    }
}

fn int_to_prelude(ity: IntTy) -> PreludeModule {
    match ity {
        IntTy::Isize => PreludeModule::Isize,
        IntTy::I8 => PreludeModule::Int8,
        IntTy::I16 => PreludeModule::Int16,
        IntTy::I32 => PreludeModule::Int32,
        IntTy::I64 => PreludeModule::Int64,
        IntTy::I128 => PreludeModule::Int128,
    }
}

fn uint_to_prelude(ity: UintTy) -> PreludeModule {
    match ity {
        UintTy::Usize => PreludeModule::Usize,
        UintTy::U8 => PreludeModule::UInt8,
        UintTy::U16 => PreludeModule::UInt16,
        UintTy::U32 => PreludeModule::UInt32,
        UintTy::U64 => PreludeModule::UInt64,
        UintTy::U128 => PreludeModule::UInt128,
    }
}

pub(crate) fn int_from_int(ity: &IntTy) -> Exp {
    match ity {
        IntTy::Isize => Exp::impure_qvar(QName::from_string("IntSize.of_int").unwrap()),
        IntTy::I8 => Exp::impure_qvar(QName::from_string("Int8.of_int").unwrap()),
        IntTy::I16 => Exp::impure_qvar(QName::from_string("Int16.of_int").unwrap()),
        IntTy::I32 => Exp::impure_qvar(QName::from_string("Int32.of_int").unwrap()),
        IntTy::I64 => Exp::impure_qvar(QName::from_string("Int64.of_int").unwrap()),
        IntTy::I128 => Exp::impure_qvar(QName::from_string("Int128.of_int").unwrap()),
    }
}

pub(crate) fn uint_from_int(uty: &UintTy) -> Exp {
    match uty {
        UintTy::Usize => Exp::impure_qvar(QName::from_string("UIntSize.of_int").unwrap()),
        UintTy::U8 => Exp::impure_qvar(QName::from_string("UInt8.of_int").unwrap()),
        UintTy::U16 => Exp::impure_qvar(QName::from_string("UInt16.of_int").unwrap()),
        UintTy::U32 => Exp::impure_qvar(QName::from_string("UInt32.of_int").unwrap()),
        UintTy::U64 => Exp::impure_qvar(QName::from_string("UInt64.of_int").unwrap()),
        UintTy::U128 => Exp::impure_qvar(QName::from_string("UInt128.of_int").unwrap()),
    }
}

pub(crate) fn int_to_int(ity: &IntTy) -> Exp {
    match ity {
        IntTy::Isize => Exp::impure_qvar(QName::from_string("IntSize.to_int").unwrap()),
        IntTy::I8 => Exp::impure_qvar(QName::from_string("Int8.to_int").unwrap()),
        IntTy::I16 => Exp::impure_qvar(QName::from_string("Int16.to_int").unwrap()),
        IntTy::I32 => Exp::impure_qvar(QName::from_string("Int32.to_int").unwrap()),
        IntTy::I64 => Exp::impure_qvar(QName::from_string("Int64.to_int").unwrap()),
        IntTy::I128 => Exp::impure_qvar(QName::from_string("Int128.to_int").unwrap()),
    }
}

pub(crate) fn uint_to_int(uty: &UintTy) -> Exp {
    match uty {
        UintTy::Usize => Exp::impure_qvar(QName::from_string("UIntSize.to_int").unwrap()),
        UintTy::U8 => Exp::impure_qvar(QName::from_string("UInt8.to_int").unwrap()),
        UintTy::U16 => Exp::impure_qvar(QName::from_string("UInt16.to_int").unwrap()),
        UintTy::U32 => Exp::impure_qvar(QName::from_string("UInt32.to_int").unwrap()),
        UintTy::U64 => Exp::impure_qvar(QName::from_string("UInt64.to_int").unwrap()),
        UintTy::U128 => Exp::impure_qvar(QName::from_string("UInt128.to_int").unwrap()),
    }
}
