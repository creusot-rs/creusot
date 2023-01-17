use crate::{
    clone_map::CloneLevel,
    ctx::{CloneMap, TranslationCtx},
    translation::{
        binop_to_binop,
        fmir::{self, Block, Branches, Expr, RValue, Statement, Terminator},
        function::{
            closure_contract, closure_generic_decls, place, place::translate_rplace_inner, promoted,
        },
        specification::{lower_impure, lower_pure},
        ty::{closure_accessors, translate_closure_ty, translate_ty},
        unop_to_unop,
    },
    util::{self, is_ghost_closure, module_name},
};
use rustc_hir::{def_id::DefId, Unsafety};
use rustc_index::vec::IndexVec;
use rustc_middle::{
    mir::{self, BasicBlock, BinOp, MirPass},
    ty::{TyKind, WithOptConstParam},
};
use rustc_mir_transform::{cleanup_post_borrowck::CleanupPostBorrowck, simplify::SimplifyCfg};
use rustc_span::DUMMY_SP;

use rustc_type_ir::{IntTy, UintTy};
use why3::{
    declaration::{CfgFunction, Decl, LetDecl, LetKind, Module, Use},
    exp::{Exp, Pattern},
    mlcfg,
    mlcfg::BlockId,
    Ident, QName,
};

use super::{clone_map2::Namer, sig_to_why3, ty, signature_of};

fn closure_ty<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> Module {
    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Body);
    let mut decls = Vec::new();

    let TyKind::Closure(_, subst) = ctx.tcx.type_of(def_id).kind() else { unreachable!() };
    let env_ty = Decl::TyDecl(translate_closure_ty(ctx, &mut names, def_id, subst));

    decls.extend(
        names
            .to_clones(ctx)
            .into_iter()
            // Definitely a hack but good enough for the moment
            .filter(|d| matches!(d, Decl::UseDecl(_))),
    );
    decls.push(env_ty);

    Module { name: format!("{}_Type", &*module_name(ctx.tcx, def_id)).into(), decls }
}

pub(crate) fn closure_aux_defs<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut Namer<'_, 'tcx>,
    def_id: DefId,
) -> Vec<Decl> {
    let mut decls = Vec::new();
    decls.push(Decl::UseDecl(Use {
        name: format!("{}_Type", &*module_name(ctx.tcx, def_id)).into(),
        as_: None,
        export: true,
    }));
    let acc: Vec<_> = closure_accessors(ctx, def_id)
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

    // decls.extend(names.to_clones(ctx));
    decls.extend(acc);
    decls.extend(contract);
    decls
}

pub(crate) fn translate_closure<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut Namer<'_, 'tcx>,
    def_id: DefId,
) -> (Module, Option<Module>) {
    assert!(ctx.is_closure(def_id));

    (closure_ty(ctx, def_id), translate_function(ctx, names, def_id))
}

pub(crate) fn translate_function<'tcx, 'sess>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut Namer<'_, 'tcx>,
    def_id: DefId,
) -> Option<Module> {
    let tcx = ctx.tcx;
    let body = to_why(ctx, names, def_id)?;

    // We use `mir_promoted` as it is the MIR required by borrowck which we will have run by this point
    let (_, promoted) = tcx.mir_promoted(WithOptConstParam::unknown(def_id.expect_local()));

    let mut decls = Vec::new();
    decls.extend(closure_generic_decls(ctx.tcx, def_id));

    if ctx.tcx.is_closure(def_id) {
        decls.extend(closure_aux_defs(ctx, names, def_id));
    }

    // let promoteds = lower_promoted(ctx, names, def_id, &*promoted.borrow());

    decls.extend(names.to_clones(ctx));
    // decls.extend(promoteds);
    decls.push(body);
    let name = module_name(ctx.tcx, def_id);
    Some(Module { name, decls })
}

fn lower_promoted<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    promoted: &IndexVec<mir::Promoted, mir::Body<'tcx>>,
) -> Vec<Decl> {
    let param_env = ctx.param_env(def_id);

    let mut decls = Vec::new();
    for p in promoted.iter_enumerated() {
        if is_ghost_closure(ctx.tcx, p.1.return_ty()).is_some() {
            continue;
        }

        let promoted = promoted::translate_promoted(ctx, names, param_env, p, def_id);
        let promoted = promoted.unwrap_or_else(|e| e.emit(ctx.tcx.sess));

        decls.push(promoted);
    }

    decls
}

pub fn to_why<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut Namer<'_, 'tcx>,
    def_id: DefId,
) -> Option<Decl> {
    if !def_id.is_local() || !util::has_body(ctx, def_id) || util::is_trusted(ctx.tcx, def_id) {
        return None;
    }

    let (mir, _) = ctx.mir_promoted(WithOptConstParam::unknown(def_id.expect_local()));
    let mut mir = mir.borrow().clone();
    CleanupPostBorrowck.run_pass(ctx.tcx, &mut mir);
    SimplifyCfg::new("verify").run_pass(ctx.tcx, &mut mir);

    let body = ctx.fmir_body(def_id).unwrap().clone();

    let vars: Vec<_> = body
        .locals
        .into_iter()
        .map(|(id, sp, ty)| (false, id, ty::translate_ty(ctx, names, sp, ty)))
        .collect();

    let entry = mlcfg::Block {
        statements: vars
            .iter()
            .skip(1)
            .take(body.arg_count)
            .map(|(_, id, _)| {
                let rhs = id.arg_name();
                mlcfg::Statement::Assign { lhs: id.ident(), rhs: Exp::impure_var(rhs) }
            })
            .collect(),
        terminator: mlcfg::Terminator::Goto(BlockId(0)),
    };

    let sig = signature_of(ctx, names, def_id);

    let func = Decl::CfgDecl(CfgFunction {
        sig,
        rec: true,
        constant: false,
        vars: vars.into_iter().map(|i| (i.0, i.1.ident(), i.2)).collect(),
        entry,
        blocks: body
            .blocks
            .into_iter()
            .map(|(bb, bbd)| (BlockId(bb.into()), bbd.to_why(ctx, names, &mir)))
            .collect(),
    });
    Some(func)
}
impl<'tcx> Expr<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut TranslationCtx<'tcx>,
        names: &mut Namer<'_, 'tcx>,
        // TODO: Get rid of this by introducing an intermediate `Place` type
        body: Option<&mir::Body<'tcx>>,
    ) -> Exp {
        match self {
            Expr::Place(pl) => {
                translate_rplace_inner(ctx, names, body.unwrap(), pl.local, pl.projection)
            }
            Expr::Move(pl) => {
                // TODO invalidate original place
                translate_rplace_inner(ctx, names, body.unwrap(), pl.local, pl.projection)
            }
            Expr::Copy(pl) => {
                translate_rplace_inner(ctx, names, body.unwrap(), pl.local, pl.projection)
            }
            Expr::BinOp(BinOp::BitAnd, ty, l, r) if ty.is_bool() => Exp::BinaryOp(
                why3::exp::BinOp::LazyAnd,
                box l.to_why(ctx, names, body),
                box r.to_why(ctx, names, body),
            ),
            Expr::BinOp(BinOp::Eq, ty, l, r) if ty.is_bool() => {
                // names.import_prelude_module(PreludeModule::Bool);
                Exp::Call(
                    box Exp::impure_qvar(QName::from_string("Bool.eqb").unwrap()),
                    vec![l.to_why(ctx, names, body), r.to_why(ctx, names, body)],
                )
            }
            Expr::BinOp(BinOp::Ne, ty, l, r) if ty.is_bool() => {
                // names.import_prelude_module(PreludeModule::Bool);
                Exp::Call(
                    box Exp::impure_qvar(QName::from_string("Bool.neqb").unwrap()),
                    vec![l.to_why(ctx, names, body), r.to_why(ctx, names, body)],
                )
            }
            Expr::BinOp(op, ty, l, r) => Exp::BinaryOp(
                binop_to_binop(ctx, ty, op),
                box l.to_why(ctx, names, body),
                box r.to_why(ctx, names, body),
            ),
            Expr::UnaryOp(op, arg) => {
                Exp::UnaryOp(unop_to_unop(op), box arg.to_why(ctx, names, body))
            }
            Expr::Constructor(id, ix, subst, args) => {
                let args = args.into_iter().map(|a| a.to_why(ctx, names, body)).collect();

                let ctor = names.constructor(id, subst, ix.as_usize());
                Exp::Constructor { ctor, args }
            }
            Expr::Call(id, subst, args) => {
                let mut args: Vec<_> =
                    args.into_iter().map(|a| a.to_why(ctx, names, body)).collect();
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
                        arg: box args.remove(0),
                        body: box Exp::Call(box Exp::impure_qvar(fname), closure_args),
                    }
                } else {
                    Exp::Call(box Exp::impure_qvar(fname), args)
                };
                exp
            }
            Expr::Constant(c) => lower_impure(ctx, names, c),
            Expr::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(ctx, names, body)).collect())
            }
            Expr::Span(sp, e) => {
                let e = e.to_why(ctx, names, body);
                ctx.attach_span(sp, e)
            } // Expr::Cast(_, _) => todo!(),
            Expr::Cast(e, source, target) => {
                let to_int = match source.kind() {
                    TyKind::Int(ity) => int_to_int(ity),
                    TyKind::Uint(uty) => uint_to_int(uty),
                    TyKind::Bool => {
                        // names.import_prelude_module(PreludeModule::Bool);
                        Exp::impure_qvar(QName::from_string("Bool.to_int").unwrap())
                    }
                    _ => ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                let from_int = match target.kind() {
                    TyKind::Int(ity) => int_from_int(ity),
                    TyKind::Uint(uty) => uint_from_int(uty),
                    TyKind::Char => {
                        // names.import_prelude_module(PreludeModule::Char);
                        Exp::impure_qvar(QName::from_string("Char.chr").unwrap())
                    }
                    _ => ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                from_int.app_to(to_int.app_to(e.to_why(ctx, names, body)))
            }
            Expr::Len(pl) => {
                let int_conversion = uint_from_int(&UintTy::Usize);
                let len_call = Exp::impure_qvar(QName::from_string("Seq.length").unwrap())
                    .app_to(pl.to_why(ctx, names, body));
                int_conversion.app_to(len_call)
            }
        }
    }

    fn invalidated_places(&self, places: &mut Vec<fmir::Place<'tcx>>) {
        match self {
            Expr::Place(_) => {}
            Expr::Move(p) => places.push(*p),
            Expr::Copy(_) => {}
            Expr::BinOp(_, _, l, r) => {
                l.invalidated_places(places);
                r.invalidated_places(places)
            }
            Expr::UnaryOp(_, e) => e.invalidated_places(places),
            Expr::Constructor(_, _, _, es) => es.iter().for_each(|e| e.invalidated_places(places)),
            Expr::Call(_, _, es) => es.iter().for_each(|e| e.invalidated_places(places)),
            Expr::Constant(_) => {}
            Expr::Cast(e, _, _) => e.invalidated_places(places),
            Expr::Tuple(es) => es.iter().for_each(|e| e.invalidated_places(places)),
            Expr::Span(_, e) => e.invalidated_places(places),
            Expr::Len(e) => e.invalidated_places(places),
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
        ctx: &mut TranslationCtx<'tcx>,
        names: &mut Namer<'_, 'tcx>,
        // TODO: Get rid of this by introducing an intermediate `Place` type
        body: Option<&mir::Body<'tcx>>,
    ) -> why3::mlcfg::Terminator {
        use why3::mlcfg::Terminator::*;
        match self {
            Terminator::Goto(bb) => Goto(BlockId(bb.into())),
            Terminator::Switch(switch, branches) => {
                let discr = switch.to_why(ctx, names, body);
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
        _: &mut TranslationCtx<'tcx>,
        names: &mut Namer<'_, 'tcx>,
        discr: Exp,
    ) -> mlcfg::Terminator {
        use why3::mlcfg::Terminator::*;

        match self {
            Branches::Int(brs, def) => {
                brs.into_iter().rfold(Goto(BlockId(def.into())), |acc, (val, bb)| {
                    Switch(
                        Exp::BinaryOp(
                            why3::exp::BinOp::Eq,
                            box discr.clone(),
                            box Exp::Const(why3::exp::Constant::Int(val, None)),
                        ),
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
                        Exp::BinaryOp(
                            why3::exp::BinOp::Eq,
                            box discr.clone(),
                            box Exp::Const(why3::exp::Constant::Uint(val, None)),
                        ),
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

                        let cons_name = names.constructor(adt.did(), substs, var.as_usize());
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
        ctx: &mut TranslationCtx<'tcx>,
        names: &mut Namer<'_, 'tcx>,
        // TODO: Get rid of this by introducing an intermediate `Place` type
        body: &mir::Body<'tcx>,
    ) -> why3::mlcfg::Block {
        mlcfg::Block {
            statements: self.stmts.into_iter().flat_map(|s| s.to_why(ctx, names, body)).collect(),
            terminator: self.terminator.to_why(ctx, names, Some(body)),
        }
    }
}

impl<'tcx> Statement<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut TranslationCtx<'tcx>,
        names: &mut Namer<'_, 'tcx>,
        // TODO: Get rid of this by introducing an intermediate `Place` type
        body: &mir::Body<'tcx>,
    ) -> Vec<mlcfg::Statement> {
        match self {
            Statement::Assignment(lhs, RValue::Borrow(rhs)) => {
                let borrow = Exp::BorrowMut(box Expr::Place(rhs).to_why(ctx, names, Some(body)));
                let reassign = Exp::Final(box Expr::Place(lhs).to_why(ctx, names, Some(body)));

                vec![
                    place::create_assign_inner(ctx, names, body, &lhs, borrow),
                    place::create_assign_inner(ctx, names, body, &rhs, reassign),
                ]
            }
            Statement::Assignment(lhs, RValue::Ghost(rhs)) => {
                let ghost = lower_pure(ctx, names, rhs);

                vec![place::create_assign_inner(ctx, names, body, &lhs, ghost)]
            }
            Statement::Assignment(lhs, RValue::Expr(rhs)) => {
                let mut invalid = Vec::new();
                rhs.invalidated_places(&mut invalid);
                let rhs = rhs.to_why(ctx, names, Some(body));
                let mut exps = vec![place::create_assign_inner(ctx, names, body, &lhs, rhs)];
                for pl in invalid {
                    let ty = translate_ty(ctx, names, DUMMY_SP, pl.ty(ctx.tcx).ty);
                    exps.push(place::create_assign_inner(ctx, names, body, &pl, Exp::Any(ty)));
                }
                exps
            }
            Statement::Resolve(id, subst, pl) => {
                let rp = Exp::impure_qvar(names.value(id, subst));

                let assume = rp.app_to(Expr::Place(pl).to_why(ctx, names, Some(body)));
                vec![mlcfg::Statement::Assume(assume)]
            }
            Statement::Assertion(a) => {
                vec![mlcfg::Statement::Assert(lower_pure(ctx, names, a))]
            }

            Statement::Invariant(nm, inv) => vec![mlcfg::Statement::Invariant(
                nm.to_string().into(),
                lower_pure(ctx, names, inv),
            )],
        }
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
