use super::{
    clone_map::PreludeModule,
    dependency::HackedId,
    signature::signature_of,
    term::{lower_impure, lower_pure},
    CloneDepth, CloneSummary, Namer, TransId, Why3Generator,
};
use crate::{
    backend::{
        closure_generic_decls, optimization,
        place::{self, translate_rplace},
        ty::{self, translate_closure_ty, translate_ty},
    },
    ctx::{BodyId, CloneMap, TranslationCtx},
    fmir::Operand,
    translation::{
        binop_to_binop,
        fmir::{
            self, Block, Branches, Expr, ExprKind, LocalDecls, Place, RValue, Statement, Terminator,
        },
        function::promoted,
        unop_to_unop,
    },
    util::{self, module_name, ItemType},
};
use rustc_hir::{def_id::DefId, Unsafety};
use rustc_middle::{
    mir::{BasicBlock, BinOp, ProjectionElem},
    ty::{GenericArgsRef, TyKind},
};
use rustc_span::{Span, DUMMY_SP};
use rustc_type_ir::{IntTy, UintTy};
use why3::{
    declaration::{self, Attribute, CfgFunction, Decl, LetDecl, LetKind, Module},
    exp::{Constant, Exp, Pattern},
    mlcfg,
    mlcfg::BlockId,
    Ident, QName,
};

use super::signature::sig_to_why3;

fn closure_ty<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Module {
    let mut names = CloneMap::new(ctx.tcx, def_id.into());
    let mut decls = Vec::new();

    let TyKind::Closure(_, subst) = ctx.type_of(def_id).instantiate_identity().kind() else {
        unreachable!()
    };
    names.insert_hidden_type(ctx.type_of(def_id).instantiate_identity());
    let env_ty = Decl::TyDecl(translate_closure_ty(ctx, &mut names, def_id, subst));

    let (clones, _) = names.to_clones(ctx, CloneDepth::Deep);
    decls.extend(
        // Definitely a hack but good enough for the moment
        clones.into_iter().filter(|d| matches!(d, Decl::UseDecl(_))),
    );
    decls.push(env_ty);

    Module { name: format!("{}_Type", &*module_name(ctx.tcx, def_id)).into(), decls }
}

pub(crate) fn closure_aux_defs<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) {
    // COMPLETE HACK. This should be properly cleaned up
    let contract = ctx.closure_contract(def_id).clone();

    // HACK RESOLVE
    let mut names = CloneMap::new(ctx.tcx, def_id.into());
    sig_to_why3(ctx, &mut names, &contract.resolve.0, def_id);
    lower_pure(ctx, &mut names, &contract.resolve.1);

    let (_, deps) = names.to_clones(ctx, CloneDepth::Shallow);
    ctx.dependencies.insert(TransId::Hacked(HackedId::Resolve, def_id), deps);

    // HACK PRECOND
    let mut names = CloneMap::new(ctx.tcx, def_id.into());
    sig_to_why3(ctx, &mut names, &contract.precond.0, def_id);
    lower_pure(ctx, &mut names, &contract.precond.1);

    let (_, deps) = names.to_clones(ctx, CloneDepth::Shallow);
    ctx.dependencies.insert(TransId::Hacked(HackedId::Precondition, def_id), deps);

    // HACK POST ONCE
    if let Some((sig, term)) = contract.postcond_once {
        let mut names = CloneMap::new(ctx.tcx, def_id.into());
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.to_clones(ctx, CloneDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(HackedId::PostconditionOnce, def_id), deps);
    }

    // HACK POST MUT
    if let Some((sig, term)) = contract.postcond_mut {
        let mut names = CloneMap::new(ctx.tcx, def_id.into());
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.to_clones(ctx, CloneDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(HackedId::PostconditionMut, def_id), deps);
    }
    // HACK POST
    if let Some((sig, term)) = contract.postcond {
        let mut names = CloneMap::new(ctx.tcx, def_id.into());
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.to_clones(ctx, CloneDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(HackedId::Postcondition, def_id), deps);
    }
    // HACK UNNEst
    if let Some((sig, term)) = contract.unnest {
        let mut names = CloneMap::new(ctx.tcx, def_id.into());
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.to_clones(ctx, CloneDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(HackedId::Unnest, def_id), deps);
    } // END COMPLETE HACK
      // decls.extend(contract);
      // decls
    for (ix, (sig, term)) in contract.accessors.into_iter().enumerate() {
        let mut names = CloneMap::new(ctx.tcx, def_id.into());
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.to_clones(ctx, CloneDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(HackedId::Accessor(ix as u8), def_id), deps);
    }
}

pub(crate) fn translate_closure<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (CloneSummary<'tcx>, Module, Option<Module>) {
    assert!(ctx.is_closure(def_id));
    let (summary, func) = translate_function(ctx, def_id);
    (summary, closure_ty(ctx, def_id), func)
}

pub(crate) fn translate_function<'tcx, 'sess>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (CloneSummary<'tcx>, Option<Module>) {
    let tcx = ctx.tcx;
    let mut names = CloneMap::new(tcx, def_id.into());

    let Some(body_ids) = collect_body_ids(ctx, def_id) else {
        let (_, clones) = names.to_clones(ctx, CloneDepth::Deep);
        return (clones, None);
    };
    let body = to_why(ctx, &mut names, body_ids[0]);

    if ctx.tcx.is_closure(def_id) {
        closure_aux_defs(ctx, def_id)
    };

    let promoteds = body_ids[1..]
        .iter()
        .map(|body_id| lower_promoted(ctx, &mut names, *body_id))
        .collect::<Vec<_>>();

    let (clones, summary) = names.to_clones(ctx, CloneDepth::Deep);

    let decls = closure_generic_decls(ctx.tcx, def_id)
        .chain(clones)
        .chain(promoteds)
        .chain(std::iter::once(body))
        .collect();

    let name = module_name(ctx.tcx, def_id);
    (summary, Some(Module { name, decls }))
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

    let mut sig = sig_to_why3(ctx, names, &sig, body_id.def_id());
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
            why3::mlcfg::Statement::Assign { lhs, rhs, attr: _ } => {
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
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut N,
        locals: &LocalDecls<'tcx>,
    ) -> Exp {
        let e = match self.kind {
            ExprKind::Operand(Operand::Move(pl)) => {
                // TODO invalidate original place
                pl.as_rplace(ctx, names, locals)
            }
            ExprKind::Operand(Operand::Copy(pl)) => pl.as_rplace(ctx, names, locals),
            ExprKind::BinOp(BinOp::BitAnd, l, r) if l.ty.is_bool() => {
                l.to_why(ctx, names, locals).lazy_and(r.to_why(ctx, names, locals))
            }
            ExprKind::BinOp(BinOp::Eq, l, r) if l.ty.is_bool() => {
                names.import_prelude_module(PreludeModule::Bool);
                Exp::impure_qvar(QName::from_string("Bool.eqb").unwrap())
                    .app(vec![l.to_why(ctx, names, locals), r.to_why(ctx, names, locals)])
            }
            ExprKind::BinOp(BinOp::Ne, l, r) if l.ty.is_bool() => {
                names.import_prelude_module(PreludeModule::Bool);
                Exp::impure_qvar(QName::from_string("Bool.neqb").unwrap())
                    .app(vec![l.to_why(ctx, names, locals), r.to_why(ctx, names, locals)])
            }
            ExprKind::BinOp(op, l, r) => {
                // Hack
                translate_ty(ctx, names, DUMMY_SP, l.ty);

                Exp::BinaryOp(
                    binop_to_binop(ctx, l.ty, op),
                    Box::new(l.to_why(ctx, names, locals)),
                    Box::new(r.to_why(ctx, names, locals)),
                )
            }
            ExprKind::UnaryOp(op, arg) => {
                Exp::UnaryOp(unop_to_unop(arg.ty, op), Box::new(arg.to_why(ctx, names, locals)))
            }
            ExprKind::Constructor(id, subst, args) => {
                let args = args.into_iter().map(|a| a.to_why(ctx, names, locals)).collect();

                let ctor = names.constructor(id, subst);
                Exp::Constructor { ctor, args }
            }
            ExprKind::Constant(c) => lower_impure(ctx, names, &c),
            ExprKind::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(ctx, names, locals)).collect())
            }
            ExprKind::Cast(e, source, target) => {
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
            ExprKind::Len(pl) => {
                let len_call = Exp::impure_qvar(QName::from_string("Slice.length").unwrap())
                    .app_to(pl.to_why(ctx, names, locals));
                len_call
            }
            ExprKind::Array(fields) => {
                let id = Ident::build("__arr_temp");
                let ty = translate_ty(ctx, names, DUMMY_SP, self.ty);

                let len = fields.len();

                let arr_var = Exp::impure_var(id.clone());
                let arr_elts =
                    Exp::RecField { record: Box::new(arr_var.clone()), label: "elts".into() };
                let fields = fields.into_iter().enumerate().map(|(ix, f)| {
                    Exp::impure_qvar(QName::from_string("Seq.get").unwrap())
                        .app(vec![arr_elts.clone(), Exp::Const(Constant::Int(ix as i128, None))])
                        .eq(f.to_why(ctx, names, locals))
                });

                Exp::Let {
                    pattern: Pattern::VarP(id.clone()),
                    arg: Box::new(Exp::Any(ty)),
                    body: Box::new(Exp::Chain(
                        fields
                            .map(|e| Exp::Assume(Box::new(e)))
                            .chain(std::iter::once(Exp::Assume(Box::new(
                                Exp::impure_qvar(QName::from_string("Slice.length").unwrap())
                                    .app_to(arr_var.clone())
                                    .eq(Exp::Const(Constant::Int(len as i128, None))),
                            ))))
                            .chain(std::iter::once(arr_var.clone()))
                            .collect(),
                    )),
                }
            }
            ExprKind::Repeat(e, len) => {
                Exp::impure_qvar(QName::from_string("Slice.create").unwrap())
                    .app_to(len.to_why(ctx, names, locals))
                    .app_to(Exp::FnLit(Box::new(e.to_why(ctx, names, locals))))
            }
        };

        if self.span != DUMMY_SP {
            ctx.attach_span(self.span, e)
        } else {
            e
        }
    }

    fn invalidated_places(&self, places: &mut Vec<(fmir::Place<'tcx>, Span)>) {
        match &self.kind {
            ExprKind::Operand(Operand::Move(p)) => places.push((p.clone(), self.span)),
            ExprKind::Operand(_) => {}
            ExprKind::BinOp(_, l, r) => {
                l.invalidated_places(places);
                r.invalidated_places(places)
            }
            ExprKind::UnaryOp(_, e) => e.invalidated_places(places),
            ExprKind::Constructor(_, _, es) => es.iter().for_each(|e| e.invalidated_places(places)),
            ExprKind::Constant(_) => {}
            ExprKind::Cast(e, _, _) => e.invalidated_places(places),
            ExprKind::Tuple(es) => es.iter().for_each(|e| e.invalidated_places(places)),
            ExprKind::Len(e) => e.invalidated_places(places),
            ExprKind::Array(f) => f.iter().for_each(|f| f.invalidated_places(places)),
            ExprKind::Repeat(e, len) => {
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
            Terminator::Abort(_) => {}
        }
    }

    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
        statements: &mut Vec<mlcfg::Statement>,
    ) -> why3::mlcfg::Terminator {
        use why3::mlcfg::Terminator::*;
        match self {
            Terminator::Goto(bb) => Goto(BlockId(bb.into())),
            Terminator::Switch(switch, branches) => {
                let discr = switch.to_why(ctx, names, locals);
                branches.to_why(ctx, names, discr)
            }
            Terminator::Return => Return,
            Terminator::Abort(span) => {
                let exp = ctx.attach_span(span, Exp::mk_false());
                statements.push(mlcfg::Statement::Assert(exp));
                Absurd
            }
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
        let mut statements = Vec::new();

        for v in self.variant.into_iter() {
            statements.push(mlcfg::Statement::Variant(lower_pure(ctx, names, &v)));
        }

        for i in self.invariants {
            statements.push(mlcfg::Statement::Invariant(lower_pure(ctx, names, &i)));
        }

        statements.extend(self.stmts.into_iter().flat_map(|s| s.to_why(ctx, names, locals)));
        let terminator = self.terminator.to_why(ctx, names, locals, &mut statements);
        mlcfg::Block { statements, terminator }
    }
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn as_rplace<N: Namer<'tcx>>(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut N,
        locals: &LocalDecls<'tcx>,
    ) -> why3::Exp {
        translate_rplace(ctx, names, locals, self.local, &self.projection)
    }
}

pub(crate) fn borrow_generated_id<V: std::fmt::Debug, T: std::fmt::Debug>(
    original_borrow: Exp,
    projection: &[ProjectionElem<V, T>],
) -> Exp {
    let mut borrow_id = Exp::Call(
        Box::new(Exp::pure_qvar(QName::from_string("Borrow.get_id").unwrap())),
        vec![original_borrow],
    );
    for proj in projection {
        match proj {
            ProjectionElem::Deref => {
                // Deref of a box
            }
            ProjectionElem::Field(idx, _) => {
                borrow_id = Exp::Call(
                    Box::new(Exp::pure_qvar(QName::from_string("Borrow.inherit_id").unwrap())),
                    vec![borrow_id, Exp::Const(Constant::Int(idx.as_u32() as i128 + 1, None))],
                );
            }
            ProjectionElem::Downcast(_, _) => {
                // since only one variant can be active at a time, there is no need to change the borrow index further
            }
            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::OpaqueCast(_) => {
                // Should only appear in logic, so we can ignore them.
            }
            ProjectionElem::Subtype(_) => {}
        }
    }
    borrow_id
}

impl<'tcx> Statement<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
    ) -> Vec<mlcfg::Statement> {
        match self {
            Statement::Assignment(lhs, RValue::Borrow(rhs), span) => {
                let borrow = Exp::Call(
                    Box::new(Exp::impure_qvar(QName::from_string("Borrow.borrow_mut").unwrap())),
                    vec![rhs.as_rplace(ctx, names, locals)],
                );
                let reassign = Exp::Final(Box::new(lhs.as_rplace(ctx, names, locals)));

                vec![
                    place::create_assign_inner(ctx, names, locals, &lhs, borrow, span),
                    place::create_assign_inner(ctx, names, locals, &rhs, reassign, span),
                ]
            }
            Statement::Assignment(lhs, RValue::FinalBorrow(rhs, deref_index), span) => {
                let original_borrow = Place {
                    local: rhs.local.clone(),
                    projection: rhs.projection[..deref_index].to_vec(),
                }
                .as_rplace(ctx, names, locals);
                let borrow_id =
                    borrow_generated_id(original_borrow, &rhs.projection[deref_index + 1..]);
                let borrow = Exp::Call(
                    Box::new(Exp::impure_qvar(QName::from_string("Borrow.borrow_final").unwrap())),
                    vec![rhs.as_rplace(ctx, names, locals), borrow_id],
                );
                let reassign = Exp::Final(Box::new(lhs.as_rplace(ctx, names, locals)));

                vec![
                    place::create_assign_inner(ctx, names, locals, &lhs, borrow, span),
                    place::create_assign_inner(ctx, names, locals, &rhs, reassign, span),
                ]
            }
            Statement::Assignment(lhs, RValue::Ghost(rhs), span) => {
                let ghost = lower_pure(ctx, names, &rhs);
                vec![place::create_assign_inner(ctx, names, locals, &lhs, ghost, span)]
            }
            Statement::Assignment(lhs, RValue::Expr(rhs), span) => {
                let mut invalid = Vec::new();
                rhs.invalidated_places(&mut invalid);
                let rhs = rhs.to_why(ctx, names, locals);
                let mut exps =
                    vec![place::create_assign_inner(ctx, names, locals, &lhs, rhs, span)];
                invalidate_places(ctx, names, locals, span, invalid, &mut exps);

                exps
            }
            Statement::Call(dest, fun_id, subst, args, span) => {
                let mut invalid = Vec::new();
                args.iter().for_each(|a| a.invalidated_places(&mut invalid));

                let mut exp = func_call_to_why3(ctx, names, locals, fun_id, subst, args);

                if let Some(attr) = ctx.span_attr(span) {
                    exp = Exp::Attr(attr, Box::new(exp));
                }

                let mut exps =
                    vec![place::create_assign_inner(ctx, names, locals, &dest, exp, span)];
                invalidate_places(ctx, names, locals, span, invalid, &mut exps);

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
                    Box::new(lower_pure(ctx, names, &cond)),
                ))]
            }
            Statement::AssumeBorrowInv(pl) => {
                let inv_fun = Exp::impure_qvar(
                    names.ty_inv(pl.ty(ctx.tcx, locals).builtin_deref(false).unwrap().ty),
                );
                let arg = Exp::Final(Box::new(pl.as_rplace(ctx, names, locals)));

                vec![mlcfg::Statement::Assume(inv_fun.app_to(arg))]
            }
            Statement::AssertTyInv(pl) => {
                let inv_fun = Exp::impure_qvar(names.ty_inv(pl.ty(ctx.tcx, locals)));
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

fn invalidate_places<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    locals: &LocalDecls<'tcx>,
    span: Span,
    invalid: Vec<(Place<'tcx>, Span)>,
    out: &mut Vec<mlcfg::Statement>,
) {
    for (pl, pl_span) in invalid {
        let ty = pl.ty(ctx.tcx, locals);
        let ty = translate_ty(ctx, names, pl_span.substitute_dummy(span), ty);
        out.push(place::create_assign_inner(ctx, names, locals, &pl, Exp::Any(ty), pl_span));
    }
}

fn func_call_to_why3<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    locals: &LocalDecls<'tcx>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Vec<Expr<'tcx>>,
) -> Exp {
    let mut args: Vec<_> = args.into_iter().map(|a| a.to_why(ctx, names, locals)).collect();
    let fname = names.value(id, subst);

    let exp = if ctx.is_closure(id) {
        assert!(args.len() == 2, "closures should only have two arguments (env, args)");

        let real_sig = ctx.signature_unclosure(subst.as_closure().sig(), Unsafety::Normal);
        let closure_arg_count = real_sig.inputs().skip_binder().len();
        let names = ('a'..).take(closure_arg_count);

        let mut closure_args = vec![args.remove(0)];

        closure_args.extend(names.clone().map(|nm| Exp::impure_var(nm.to_string().into())));

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

pub(crate) fn int_to_prelude(ity: IntTy) -> PreludeModule {
    match ity {
        IntTy::Isize => PreludeModule::Isize,
        IntTy::I8 => PreludeModule::Int8,
        IntTy::I16 => PreludeModule::Int16,
        IntTy::I32 => PreludeModule::Int32,
        IntTy::I64 => PreludeModule::Int64,
        IntTy::I128 => PreludeModule::Int128,
    }
}

pub(crate) fn uint_to_prelude(ity: UintTy) -> PreludeModule {
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
