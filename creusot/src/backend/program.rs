use super::{
    clone_map::PreludeModule, dependency::HackedId, place::rplace_to_expr, signature::signature_of,
    term::lower_pure, CloneDepth, CloneSummary, Namer, TransId, Why3Generator,
};
use crate::{
    backend::{
        closure_generic_decls, optimization,
        place::{self, translate_rplace},
        ty::{self, translate_closure_ty, translate_ty},
        wto::weak_topological_order,
    },
    ctx::{BodyId, CloneMap, TranslationCtx},
    fmir::{Body, BorrowKind, Operand},
    translation::{
        fmir::{self, Block, Branches, LocalDecls, Place, RValue, Statement, Terminator},
        function::promoted,
        unop_to_unop,
    },
    util::{self, module_name},
};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{self, BasicBlock, BinOp, ProjectionElem, START_BLOCK},
    ty::{AdtDef, GenericArgsRef, Ty, TyKind},
};
use rustc_span::{Span, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{FloatTy, IntTy, UintTy};
use why3::{
    coma::{self, Arg, Defn, Expr, Param},
    declaration::{Attribute, Decl, LetDecl, LetKind, Module, Signature},
    exp::{Constant, Exp, Pattern},
    ty::Type,
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
    assert!(ctx.is_closure_or_coroutine(def_id));
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

    if ctx.tcx.is_closure_or_coroutine(def_id) {
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
        if util::snapshot_closure_id(ctx.tcx, *p_ty).is_none() {
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
    let (sig, fmir) = promoted.unwrap_or_else(|e| e.emit(ctx.tcx));

    let mut sig = sig_to_why3(ctx, names, &sig, body_id.def_id());
    sig.name = format!("promoted{:?}", body_id.promoted.unwrap().as_usize()).into();

    let mut previous_block = None;

    let mut exp = Exp::var("_0");
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
            IntermediateStmt::Assign(ident, exp) => {
                Exp::Let { pattern: Pattern::VarP(ident), arg: Box::new(exp), body: Box::new(acc) }
            }
            IntermediateStmt::Call(_, _, _) => todo!("promoted call"),
            IntermediateStmt::Assume(_) => acc,
            IntermediateStmt::Assert(_) => {
                ctx.crash_and_error(ctx.def_span(body_id.def_id()), "unsupported promoted constant")
            }
            IntermediateStmt::Any(_, _) => todo!(),
            // why3::mlcfg::Statement::Assign { lhs, rhs, attr: _ } => {
            //     Exp::Let { pattern: Pattern::VarP(lhs), arg: Box::new(rhs), body: Box::new(acc) }
            // }
            // why3::mlcfg::Statement::Assume(_) => acc,
            // why3::mlcfg::Statement::Invariant(_)
            // | why3::mlcfg::Statement::Variant(_)
            // | why3::mlcfg::Statement::Assert(_) => {
            //     ctx.crash_and_error(ctx.def_span(body_id.def_id()), "unsupported promoted constant")
            // }
        });
    }

    Decl::ConstantDecl(why3::declaration::Constant {
        name: sig.name,
        type_: sig.retty.unwrap(),
        body: exp,
    })
}

pub fn val<'tcx>(_: &mut Why3Generator<'tcx>, sig: Signature) -> Decl {
    let params = sig
        .args
        .into_iter()
        .flat_map(|b| b.var_type_pairs())
        .map(|(v, ty)| Param::Term(v, ty))
        .chain([Param::Cont(
            "return".into(),
            Vec::new(),
            vec![Param::Term("ret".into(), sig.retty.clone().unwrap())],
        )])
        .collect();

    use coma::*;
    let mut body = Expr::Any;

    body = sig
        .contract
        .requires
        .into_iter()
        .fold(body, |acc, ensures| Expr::Assert(Box::new(ensures), Box::new(acc)));

    let mut postcond = Expr::Symbol("return".into()).app(vec![Arg::Term(Exp::var("result"))]);
    postcond = Expr::BlackBox(Box::new(postcond));
    postcond = sig
        .contract
        .ensures
        .into_iter()
        .fold(postcond, |acc, ensures| Expr::Assert(Box::new(ensures), Box::new(acc)));

    let body = Expr::Defn(
        Box::new(body),
        false,
        vec![Defn {
            name: "return".into(),
            writes: Vec::new(),
            params: vec![Param::Term("result".into(), sig.retty.clone().unwrap())],
            body: postcond,
        }],
    );
    why3::declaration::Decl::Coma(Defn { name: sig.name, writes: Vec::new(), params, body })
}

pub fn to_why<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    body_id: BodyId,
) -> Decl {
    let mut body = ctx.fmir_body(body_id).unwrap().clone();

    let usage = optimization::gather_usage(&body);
    optimization::simplify_fmir(usage, &mut body);

    use petgraph::graphmap::DiGraphMap;

    fn node_graph(x: &Body) -> petgraph::graphmap::DiGraphMap<BasicBlock, ()> {
        let mut graph = DiGraphMap::default();
        for (bb, data) in &x.blocks {
            graph.add_node(*bb);
            for tgt in data.terminator.targets() {
                graph.add_edge(*bb, tgt, ());
            }
        }

        graph
    }

    let wto = weak_topological_order(&node_graph(&body), START_BLOCK);

    let blocks: Vec<Defn> =
        wto.into_iter().map(|c| component_to_defn(&mut body, ctx, names, c)).collect();

    let vars: Vec<_> = body
        .locals
        .into_iter()
        .map(|(id, decl)| {
            let ty = ty::translate_ty(ctx, names, decl.span, decl.ty);

            let init = if decl.arg {
                Exp::var(Ident::build(id.as_str()))
            } else {
                names.import_prelude_module(PreludeModule::Intrinsic);
                Exp::var("any_l").app_to(Exp::Tuple(Vec::new())).ascribe(ty.clone())
            };
            coma::Var(Ident::build(id.as_str()), ty.clone(), init, coma::IsRef::Ref)
        })
        .collect();

    let body = Expr::Defn(Box::new(Expr::Symbol("bb0".into())), true, blocks);
    let sig = signature_of(ctx, names, body_id.def_id());

    let mut postcond = Expr::Symbol("return".into()).app(vec![Arg::Term(Exp::var("_0"))]);

    postcond = Expr::BlackBox(Box::new(postcond));
    postcond = sig
        .contract
        .ensures
        .into_iter()
        .fold(postcond, |acc, ensures| Expr::Assert(Box::new(ensures), Box::new(acc)));

    let mut body = Expr::Defn(
        Box::new(Expr::BlackBox(Box::new(body))),
        false,
        vec![Defn {
            name: "return".into(),
            writes: Vec::new(),
            params: vec![Param::Term("result".into(), sig.retty.clone().unwrap())],
            body: postcond,
        }],
    );

    body = sig
        .contract
        .requires
        .into_iter()
        .fold(body, |acc, req| Expr::Assert(Box::new(req), Box::new(acc)));

    let body = Expr::Let(Box::new(body), vars);

    let params = sig
        .args
        .into_iter()
        .flat_map(|b| b.var_type_pairs())
        .map(|(v, ty)| Param::Term(v, ty))
        .chain([Param::Cont(
            "return".into(),
            Vec::new(),
            vec![Param::Term("ret".into(), sig.retty.unwrap())],
        )])
        .collect();
    Decl::Coma(coma::Defn { name: sig.name, writes: Vec::new(), params, body })

    // Decl::CfgDecl(CfgFunction { sig, rec: true, constant: false, entry, blocks, vars })
}

use super::wto::Component;

fn component_to_defn<'tcx>(
    body: &mut Body<'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    c: Component<BasicBlock>,
) -> coma::Defn {
    let (head, tl) = match c {
        Component::Vertex(v) => {
            let block = body.blocks.remove(&v).unwrap();
            return block.to_why(ctx, names, &body.locals, v);
        }
        Component::Component(v, tls) => (v, tls),
    };

    let defns = tl.into_iter().map(|id| component_to_defn(body, ctx, names, id)).collect();

    let block = body.blocks.remove(&head).unwrap();
    let mut block = block.to_why(ctx, names, &body.locals, head);

    block.body = Expr::Defn(Box::new(block.body), true, defns);

    block
}

impl<'tcx> Operand<'tcx> {
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut N,
        locals: &LocalDecls<'tcx>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> Exp {
        match self {
            Operand::Move(pl) => pl.as_rplace(ctx, names, locals, istmts),
            Operand::Copy(pl) => pl.as_rplace(ctx, names, locals, istmts),
            Operand::Constant(c) => lower_pure(ctx, names, &c),
        }
    }
    fn invalidated_places(&self, places: &mut Vec<fmir::Place<'tcx>>) {
        if let Operand::Move(pl) = self {
            places.push(pl.clone())
        }
    }
}

impl<'tcx> RValue<'tcx> {
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut N,
        locals: &LocalDecls<'tcx>,
        ty: Ty<'tcx>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> Exp {
        let e = match self {
            RValue::Operand(op) => op.to_why(ctx, names, locals, istmts),
            RValue::BinOp(BinOp::BitAnd, l, r) if l.ty(ctx.tcx, locals).is_bool() => {
                l.to_why(ctx, names, locals, istmts).lazy_and(r.to_why(ctx, names, locals, istmts))
            }
            RValue::BinOp(BinOp::Eq, l, r) if l.ty(ctx.tcx, locals).is_bool() => {
                names.import_prelude_module(PreludeModule::Bool);

                Exp::qvar(QName::from_string("Bool.eq").unwrap()).app(vec![
                    l.to_why(ctx, names, locals, istmts),
                    r.to_why(ctx, names, locals, istmts),
                ])
            }
            RValue::BinOp(BinOp::Ne, l, r) if l.ty(ctx.tcx, locals).is_bool() => {
                names.import_prelude_module(PreludeModule::Bool);

                Exp::qvar(QName::from_string("Bool.ne").unwrap()).app(vec![
                    l.to_why(ctx, names, locals, istmts),
                    r.to_why(ctx, names, locals, istmts),
                ])
            }
            RValue::BinOp(_, _, _) => {
                // let ty = l.ty(ctx.tcx, locals);
                // // Hack
                // translate_ty(ctx, names, DUMMY_SP, ty);
                unreachable!()
                // let op_ty = l.ty(ctx.tcx, locals);
                // // Hack
                // translate_ty(ctx, names, DUMMY_SP, op_ty);
            }
            RValue::UnaryOp(op, arg) => Exp::UnaryOp(
                unop_to_unop(arg.ty(ctx.tcx, locals), op),
                Box::new(arg.to_why(ctx, names, locals, istmts)),
            ),

            RValue::Constructor(id, subst, args) => {
                let needs_ty = ctx.generics_of(id).count() > 0 && args.len() == 0;
                let args = args.into_iter().map(|a| a.to_why(ctx, names, locals, istmts)).collect();

                let ctor = names.constructor(id, subst);
                let cons = Exp::Constructor { ctor, args };
                if needs_ty {
                    cons.ascribe(translate_ty(ctx, names, DUMMY_SP, ty))
                } else {
                    cons
                }
            }
            RValue::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(ctx, names, locals, istmts)).collect())
            }
            RValue::Cast(e, source, target) => {
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
                        Exp::qvar(QName::from_string("Bool.to_int").unwrap())
                    }
                    _ => ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                let from_int = match target.kind() {
                    TyKind::Int(ity) => int_from_int(ity),
                    TyKind::Uint(uty) => uint_from_int(uty),
                    TyKind::Char => {
                        names.import_prelude_module(PreludeModule::Char);
                        Exp::qvar(QName::from_string("Char.chr").unwrap())
                    }
                    _ => ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                from_int.app_to(to_int.app_to(e.to_why(ctx, names, locals, istmts)))
            }
            RValue::Len(pl) => {
                let len_call = Exp::qvar(QName::from_string("Slice.length").unwrap())
                    .app_to(pl.to_why(ctx, names, locals, istmts));
                len_call
            }
            RValue::Array(fields) => {
                let id = Ident::build("__arr_temp");
                let ty = translate_ty(ctx, names, DUMMY_SP, ty);

                let len = fields.len();

                let arr_var = Exp::var(id.clone());
                let arr_elts =
                    Exp::RecField { record: Box::new(arr_var.clone()), label: "elts".into() };
                let fields = fields.into_iter().enumerate().map(|(ix, f)| {
                    Exp::qvar(QName::from_string("Seq.get").unwrap())
                        .app(vec![arr_elts.clone(), Exp::Const(Constant::Int(ix as i128, None))])
                        .eq(f.to_why(ctx, names, locals, istmts))
                });

                Exp::Let {
                    pattern: Pattern::VarP(id.clone()),
                    arg: Box::new(Exp::Any(ty)),
                    body: Box::new(Exp::Chain(
                        fields
                            .map(|e| Exp::Assume(Box::new(e)))
                            .chain(std::iter::once(Exp::Assume(Box::new(
                                Exp::qvar(QName::from_string("Slice.length").unwrap())
                                    .app_to(arr_var.clone())
                                    .eq(Exp::Const(Constant::Int(len as i128, None))),
                            ))))
                            .chain(std::iter::once(arr_var.clone()))
                            .collect(),
                    )),
                }
            }
            RValue::Repeat(e, len) => Exp::qvar(QName::from_string("Slice.create").unwrap())
                .app_to(len.to_why(ctx, names, locals, istmts))
                .app_to(Exp::FnLit(Box::new(e.to_why(ctx, names, locals, istmts)))),
            RValue::Ghost(t) => lower_pure(ctx, names, &t),
            RValue::Borrow(_, _) => todo!(),
        };

        e
    }

    /// Gather the set of places which are moved out of by an expression
    fn invalidated_places(&self, places: &mut Vec<fmir::Place<'tcx>>) {
        match &self {
            RValue::Operand(op) => op.invalidated_places(places),
            RValue::BinOp(_, l, r) => {
                l.invalidated_places(places);
                r.invalidated_places(places)
            }
            RValue::UnaryOp(_, e) => e.invalidated_places(places),
            RValue::Constructor(_, _, es) => es.iter().for_each(|e| e.invalidated_places(places)),
            RValue::Cast(e, _, _) => e.invalidated_places(places),
            RValue::Tuple(es) => es.iter().for_each(|e| e.invalidated_places(places)),
            RValue::Len(e) => e.invalidated_places(places),
            RValue::Array(f) => f.iter().for_each(|f| f.invalidated_places(places)),
            RValue::Repeat(e, len) => {
                e.invalidated_places(places);
                len.invalidated_places(places)
            }
            RValue::Ghost(_) => {}
            RValue::Borrow(_, _) => {}
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
    ) -> coma::Expr {
        use coma::*;
        match self {
            Terminator::Goto(bb) => Expr::Symbol(format!("bb{}", bb.as_usize()).into()),
            Terminator::Switch(switch, branches) => {
                let discr = switch.to_why(ctx, names, locals, &mut vec![]);
                branches.to_why(ctx, names, discr)
            }
            Terminator::Return => {
                Expr::Symbol("return".into()).app(vec![Arg::Term(Exp::var("_0"))])
            }
            Terminator::Abort(span) => {
                let exp = ctx.attach_span(span, Exp::mk_false());
                Expr::Assert(Box::new(exp), Box::new(Expr::Any))
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
    ) -> coma::Expr {
        use coma::Expr;
        match self {
            Branches::Int(brs, def) => {
                let mut brs = mk_switch_branches(
                    discr,
                    brs.into_iter().map(|(val, tgt)| (Exp::int(val), mk_goto(tgt))).collect(),
                );

                brs.push(Defn {
                    name: "default".into(),
                    writes: Vec::new(),
                    params: Vec::new(),
                    body: Expr::BlackBox(Box::new(mk_goto(def))),
                });
                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
            Branches::Uint(brs, def) => {
                let mut brs = mk_switch_branches(
                    discr,
                    brs.into_iter().map(|(val, tgt)| (Exp::uint(val), mk_goto(tgt))).collect(),
                );

                brs.push(Defn {
                    name: "default".into(),
                    writes: Vec::new(),
                    params: Vec::new(),
                    body: Expr::BlackBox(Box::new(mk_goto(def))),
                });
                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
            Branches::Constructor(adt, _substs, vars, def) => {
                let mut brs = mk_adt_switch(
                    _ctx,
                    names,
                    adt,
                    _substs,
                    discr,
                    vars.into_iter().map(|(var, bb)| (var, mk_goto(bb))).collect(),
                );

                brs.push(Defn {
                    name: "default".into(),
                    writes: Vec::new(),
                    params: Vec::new(),
                    body: Expr::BlackBox(Box::new(mk_goto(def))),
                });
                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
            Branches::Bool(f, t) => {
                let brs = mk_switch_branches(
                    discr,
                    vec![(Exp::mk_false(), mk_goto(f)), (Exp::mk_true(), mk_goto(t))],
                );

                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
        }
    }
}

fn mk_goto(bb: BasicBlock) -> coma::Expr {
    coma::Expr::Symbol(format!("bb{}", bb.as_u32()).into())
}

fn mk_adt_switch<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    adt: AdtDef<'tcx>,
    subst: GenericArgsRef<'tcx>,
    discr: Exp,
    brch: Vec<(VariantIdx, coma::Expr)>,
) -> Vec<coma::Defn> {
    let mut out = Vec::new();

    for (c, (ix, tgt)) in brch.into_iter().enumerate() {
        let var = &adt.variants()[ix];

        let params: Vec<coma::Param> = ('a'..)
            .zip(var.fields.iter())
            .map(|(nm, field)| {
                Param::Term(
                    nm.to_string().into(),
                    translate_ty(ctx, names, DUMMY_SP, field.ty(ctx.tcx, subst)),
                )
            })
            .collect();

        let cons = names.constructor(var.def_id, subst);

        let filter = Exp::qvar(cons)
            .app(params.iter().zip('a'..).map(|(_, nm)| Exp::var(nm.to_string())).collect());
        let filter = coma::Expr::Assert(
            Box::new(discr.clone().eq(filter)),
            Box::new(coma::Expr::BlackBox(Box::new(tgt))),
        );

        let branch =
            coma::Defn { name: format!("br{c}").into(), writes: Vec::new(), params, body: filter };
        out.push(branch)
    }
    out
}

fn mk_switch_branches(discr: Exp, brch: Vec<(Exp, coma::Expr)>) -> Vec<coma::Defn> {
    let mut out = Vec::new();
    for (ix, (cond, tgt)) in brch.into_iter().enumerate() {
        let filter = coma::Expr::Assert(
            Box::new(discr.clone().eq(cond)),
            Box::new(coma::Expr::BlackBox(Box::new(tgt))),
        );

        let branch = coma::Defn {
            name: format!("br{ix}").into(),
            writes: Vec::new(),
            params: Vec::new(),
            body: filter,
        };
        out.push(branch)
    }
    out
}

impl<'tcx> Block<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
        id: BasicBlock,
    ) -> coma::Defn {
        // for v in self.variant.into_iter() {
        //     statements.push(mlcfg::Statement::Variant(lower_pure(ctx, names, &v)));
        // }

        let terminator = self.terminator.to_why(ctx, names, locals);
        let statements = self.stmts.into_iter().flat_map(|s| s.to_why(ctx, names, locals));
        use coma::*;
        let mut body = statements.rfold(terminator, |tail, stmt| match stmt {
            IntermediateStmt::Assign(id, exp) => tail.assign(id, exp),
            IntermediateStmt::Call(params, fun, args) => {
                let c = Expr::Lambda(params, Box::new(tail));

                args.into_iter()
                    .chain(std::iter::once(Arg::Cont(c)))
                    .fold(fun, |acc, arg| Expr::App(Box::new(acc), Box::new(arg)))
            }
            IntermediateStmt::Assume(e) => {
                use coma::*;
                let assume = Expr::Assume(Box::new(e), Box::new(tail));
                assume
            }
            IntermediateStmt::Assert(e) => Expr::Assert(Box::new(e), Box::new(tail)),
            IntermediateStmt::Any(id, ty) => Expr::Defn(
                Box::new(Expr::Any),
                false,
                vec![Defn {
                    name: "any_".into(),
                    writes: vec![],
                    params: vec![Param::Term(id, ty)],
                    body: tail,
                }],
            ),
        });

        if !self.invariants.is_empty() {
            body = Expr::BlackBox(Box::new(body));
        }

        for i in self.invariants {
            body = Expr::Assert(Box::new(lower_pure(ctx, names, &i)), Box::new(body));
        }

        coma::Defn {
            name: format!("bb{}", id.as_usize()).into(),
            writes: Vec::new(),
            params: Vec::new(),
            body,
        }
    }
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn as_rplace<N: Namer<'tcx>>(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut N,
        locals: &LocalDecls<'tcx>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> why3::Exp {
        let (e, t) = rplace_to_expr(ctx, names, locals, self.local, &self.projection);
        istmts.extend(t);
        e
    }
}

pub(crate) fn borrow_generated_id<V: std::fmt::Debug, T: std::fmt::Debug>(
    original_borrow: Exp,
    projection: &[ProjectionElem<V, T>],
) -> Exp {
    let mut borrow_id = Exp::Call(
        Box::new(Exp::qvar(QName::from_string("Borrow.get_id").unwrap())),
        vec![original_borrow],
    );
    for proj in projection {
        match proj {
            ProjectionElem::Deref => {
                // Deref of a box
            }
            ProjectionElem::Field(idx, _) => {
                borrow_id = Exp::Call(
                    Box::new(Exp::qvar(QName::from_string("Borrow.inherit_id").unwrap())),
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

pub(crate) enum IntermediateStmt {
    // [ id = E] K
    Assign(Ident, Exp),
    // E [ARGS] (id : ty -> K)
    Call(Vec<coma::Param>, coma::Expr, Vec<coma::Arg>),
    // -{ E }- K
    Assume(Exp),
    // { E } K
    Assert(Exp),

    Any(Ident, Type),
}

impl IntermediateStmt {
    fn call(id: Ident, exp: Type, f: coma::Expr, args: Vec<coma::Arg>) -> Self {
        IntermediateStmt::Call(vec![Param::Term(id, exp)], f, args)
    }
}

impl<'tcx> Statement<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        locals: &LocalDecls<'tcx>,
    ) -> Vec<IntermediateStmt> {
        match self {
            Statement::Assignment(lhs, RValue::BinOp(op, l, r), span) => {
                let mut istmts = Vec::new();
                let assign =
                    place::create_assign_inner(ctx, names, locals, &lhs, Exp::var("_ret'"), span);
                let fname = binop_to_binop(names, l.ty(ctx.tcx, locals), op);
                // TODO Switch coma ast to QNames
                let call = coma::Expr::Symbol(fname);

                let args = vec![
                    Arg::Term(l.to_why(ctx, names, locals, &mut istmts)),
                    Arg::Term(r.to_why(ctx, names, locals, &mut istmts)),
                ];
                istmts.extend([IntermediateStmt::call(
                    "_ret'".into(),
                    translate_ty(ctx, names, DUMMY_SP, lhs.ty(ctx.tcx, locals)),
                    call,
                    args,
                )]);
                istmts.extend(assign);
                istmts
            }
            Statement::Assignment(lhs, RValue::Borrow(BorrowKind::Mut, rhs), span) => {
                let borrow_mut =
                    coma::Expr::Symbol(QName::from_string("Borrow.borrow_mut").unwrap());

                let mut istmts = Vec::new();
                let args = vec![
                    Arg::Ty(translate_ty(ctx, names, DUMMY_SP, rhs.ty(ctx.tcx, locals))),
                    Arg::Term(rhs.as_rplace(ctx, names, locals, &mut istmts)),
                ];
                let reassign = Exp::Final(Box::new(lhs.as_rplace(ctx, names, locals, &mut istmts)));

                let ty = lhs.ty(ctx.tcx, locals);

                let borrow_call = IntermediateStmt::call(
                    "_ret'".into(),
                    translate_ty(ctx, names, DUMMY_SP, ty),
                    borrow_mut,
                    args,
                );

                istmts.extend([borrow_call]);

                istmts.extend(place::create_assign_inner(ctx, names, locals, &rhs, reassign, span));
                istmts.extend(place::create_assign_inner(
                    ctx,
                    names,
                    locals,
                    &lhs,
                    Exp::var("_ret'"),
                    span,
                ));
                istmts
            }
            Statement::Assignment(
                lhs,
                RValue::Borrow(BorrowKind::Final(deref_index), rhs),
                span,
            ) => {
                let mut istmts = Vec::new();

                let original_borrow = Place {
                    local: rhs.local.clone(),
                    projection: rhs.projection[..deref_index].to_vec(),
                }
                .as_rplace(ctx, names, locals, &mut istmts);

                let ty = lhs.ty(ctx.tcx, locals);

                let borrow_id =
                    borrow_generated_id(original_borrow, &rhs.projection[deref_index + 1..]);
                let reassign = Exp::Final(Box::new(lhs.as_rplace(ctx, names, locals, &mut istmts)));

                let assign1 = {
                    place::create_assign_inner(ctx, names, locals, &lhs, Exp::var("_ret'"), span)
                };

                let assign2 =
                    { place::create_assign_inner(ctx, names, locals, &rhs, reassign, span) };

                let borrow_mut =
                    coma::Expr::Symbol(QName::from_string("Borrow.borrow_final").unwrap());

                let args = vec![
                    Arg::Ty(translate_ty(ctx, names, DUMMY_SP, rhs.ty(ctx.tcx, locals))),
                    Arg::Term(rhs.as_rplace(ctx, names, locals, &mut istmts)),
                    Arg::Term(borrow_id),
                ];

                let borrow_call = IntermediateStmt::call(
                    "_ret'".into(),
                    translate_ty(ctx, names, DUMMY_SP, ty),
                    borrow_mut,
                    args,
                );

                istmts.extend([borrow_call]);
                istmts.extend(assign1);
                istmts.extend(assign2);
                istmts
            }
            Statement::Assignment(lhs, e, span) => {
                let mut istmts = Vec::new();

                let mut invalid = Vec::new();
                e.invalidated_places(&mut invalid);

                let rhs = e.to_why(ctx, names, locals, lhs.ty(ctx.tcx, locals), &mut istmts);
                let assign = place::create_assign_inner(ctx, names, locals, &lhs, rhs, span);
                istmts.extend(assign);
                invalidate_places(ctx, names, locals, span, invalid, &mut istmts);

                istmts
            }
            Statement::Call(dest, fun_id, subst, args, span) => {
                let mut istmts = Vec::new();

                let (fun_exp, args) =
                    func_call_to_why3(ctx, names, locals, fun_id, subst, args, &mut istmts);
                let ty = dest.ty(ctx.tcx, locals);
                let ty = translate_ty(ctx, names, span, ty);
                let assign =
                    place::create_assign_inner(ctx, names, locals, &dest, Exp::var("_ret'"), span);

                istmts.extend([IntermediateStmt::call("_ret'".into(), ty, fun_exp, args)]);
                istmts.extend(assign);
                istmts
            }
            Statement::Resolve(id, subst, pl) => {
                ctx.translate(id);
                let mut istmts = Vec::new();

                let rp = Exp::qvar(names.value(id, subst));

                let assume = rp.app_to(pl.as_rplace(ctx, names, locals, &mut istmts));
                vec![IntermediateStmt::Assume(assume)]
            }
            Statement::Assertion { cond, msg } => {
                vec![IntermediateStmt::Assert(Exp::Attr(
                    Attribute::Attr(format!("expl:{msg}")),
                    Box::new(lower_pure(ctx, names, &cond)),
                ))]
            }
            Statement::AssumeBorrowInv(pl) => {
                let inv_fun = Exp::qvar(
                    names.ty_inv(pl.ty(ctx.tcx, locals).builtin_deref(false).unwrap().ty),
                );
                let mut istmts = Vec::new();

                let arg = Exp::Final(Box::new(pl.as_rplace(ctx, names, locals, &mut istmts)));

                istmts.extend(vec![IntermediateStmt::Assume(inv_fun.app_to(arg))]);
                istmts
            }
            Statement::AssertTyInv(pl) => {
                let inv_fun = Exp::qvar(names.ty_inv(pl.ty(ctx.tcx, locals)));
                let mut istmts = Vec::new();

                let arg = pl.as_rplace(ctx, names, locals, &mut istmts);
                let exp = Exp::Attr(
                    Attribute::Attr(format!("expl:type invariant")),
                    Box::new(inv_fun.app_to(arg)),
                );

                istmts.extend(vec![IntermediateStmt::Assert(exp)]);
                istmts
            }
            Statement::Assignment(lhs, RValue::Ghost(rhs), span) => {
                let ghost = lower_pure(ctx, names, &rhs);
                let assign = place::create_assign_inner(ctx, names, locals, &lhs, ghost, span);

                assign
            }
        }
    }
}

fn invalidate_places<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    locals: &LocalDecls<'tcx>,
    span: Span,
    invalid: Vec<Place<'tcx>>,
    out: &mut Vec<IntermediateStmt>,
) {
    // any (x -> lhs = x )
    for pl in invalid {
        let ty = pl.ty(ctx.tcx, locals);
        let ty = translate_ty(ctx, names, DUMMY_SP.substitute_dummy(span), ty);

        let assign =
            place::create_assign_inner(ctx, names, locals, &pl, Exp::var("_any"), DUMMY_SP);
        out.push(IntermediateStmt::Any("_any".into(), ty));
        out.extend(assign);
    }
}

fn func_call_to_why3<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    locals: &LocalDecls<'tcx>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Vec<Operand<'tcx>>,
    istmts: &mut Vec<IntermediateStmt>,
) -> (coma::Expr, Vec<coma::Arg>) {
    let args: Vec<_> = args
        .into_iter()
        .map(|a| a.to_why(ctx, names, locals, istmts))
        .map(|a| coma::Arg::Term(a))
        .collect();

    let fname = names.value(id, subst);

    (coma::Expr::Symbol(fname), args)
}

pub(crate) fn binop_to_binop(names: &mut CloneMap<'_>, ty: Ty, op: mir::BinOp) -> QName {
    let prelude: PreludeModule = match ty.kind() {
        TyKind::Int(ity) => int_to_prelude(*ity),
        TyKind::Uint(uty) => uint_to_prelude(*uty),
        TyKind::Float(FloatTy::F32) => PreludeModule::Float32,
        TyKind::Float(FloatTy::F64) => PreludeModule::Float64,
        TyKind::Bool => PreludeModule::Bool,
        _ => unreachable!("non-primitive type for binary operation {op:?} {ty:?}"),
    };

    names.import_prelude_module(prelude);
    let mut module = prelude.qname();

    match op {
        BinOp::Add => module.push_ident("add"),
        BinOp::AddUnchecked => module.push_ident("add"),
        BinOp::Sub => module.push_ident("sub"),
        BinOp::SubUnchecked => module.push_ident("sub"),
        BinOp::Mul => module.push_ident("mul"),
        BinOp::MulUnchecked => module.push_ident("mul"),
        BinOp::Div => module.push_ident("div"),
        BinOp::Rem => module.push_ident("rem"),
        BinOp::BitXor => module.push_ident("bw_xor"),
        BinOp::BitAnd => module.push_ident("bw_and"),
        BinOp::BitOr => module.push_ident("bw_or"),
        BinOp::Shl => module.push_ident("shl"),
        BinOp::ShlUnchecked => module.push_ident("shl"),
        BinOp::Shr => module.push_ident("shr"),
        BinOp::ShrUnchecked => module.push_ident("shr"),
        BinOp::Eq => module.push_ident("eq"),
        BinOp::Lt => module.push_ident("lt"),
        BinOp::Le => module.push_ident("le"),
        BinOp::Ne => module.push_ident("ne"),
        BinOp::Ge => module.push_ident("ge"),
        BinOp::Gt => module.push_ident("gt"),
        BinOp::Offset => unimplemented!("pointer offsets are unsupported"),
    };

    module = module.without_search_path();
    module
}

// pub(crate) fn unop_to_unop(ty: Ty, op: rustc_middle::mir::UnOp, e: Exp) -> Exp {
//     let prelude: PreludeModule = match ty.kind() {
//         TyKind::Int(ity) => int_to_prelude(*ity),
//         TyKind::Uint(uty) => uint_to_prelude(*uty),
//         TyKind::Float(FloatTy::F32) => PreludeModule::Float32,
//         TyKind::Float(FloatTy::F64) => PreludeModule::Float64,
//         TyKind::Bool => {
//             assert_eq!(op, mir::UnOp::Not);
//             PreludeModule::Bool
//         }
//         _ => unreachable!("non-primitive type for unary operation"),
//     };

//     let mut module = prelude.qname();

//     match op {
//         mir::UnOp::Not => Exp::UnaryOp(UnOp::Not, Box::new(e)),
//         mir::UnOp::Neg => {
//             module.push_ident("neg");

//             module = module.without_search_path();
//             Exp::imqvar(module).app_to(e)
//         }
//     }
// }

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
        IntTy::Isize => Exp::qvar(QName::from_string("IntSize.of_int").unwrap()),
        IntTy::I8 => Exp::qvar(QName::from_string("Int8.of_int").unwrap()),
        IntTy::I16 => Exp::qvar(QName::from_string("Int16.of_int").unwrap()),
        IntTy::I32 => Exp::qvar(QName::from_string("Int32.of_int").unwrap()),
        IntTy::I64 => Exp::qvar(QName::from_string("Int64.of_int").unwrap()),
        IntTy::I128 => Exp::qvar(QName::from_string("Int128.of_int").unwrap()),
    }
}

pub(crate) fn uint_from_int(uty: &UintTy) -> Exp {
    match uty {
        UintTy::Usize => Exp::qvar(QName::from_string("UIntSize.of_int").unwrap()),
        UintTy::U8 => Exp::qvar(QName::from_string("UInt8.of_int").unwrap()),
        UintTy::U16 => Exp::qvar(QName::from_string("UInt16.of_int").unwrap()),
        UintTy::U32 => Exp::qvar(QName::from_string("UInt32.of_int").unwrap()),
        UintTy::U64 => Exp::qvar(QName::from_string("UInt64.of_int").unwrap()),
        UintTy::U128 => Exp::qvar(QName::from_string("UInt128.of_int").unwrap()),
    }
}

pub(crate) fn int_to_int(ity: &IntTy) -> Exp {
    match ity {
        IntTy::Isize => Exp::qvar(QName::from_string("IntSize.to_int").unwrap()),
        IntTy::I8 => Exp::qvar(QName::from_string("Int8.to_int").unwrap()),
        IntTy::I16 => Exp::qvar(QName::from_string("Int16.to_int").unwrap()),
        IntTy::I32 => Exp::qvar(QName::from_string("Int32.to_int").unwrap()),
        IntTy::I64 => Exp::qvar(QName::from_string("Int64.to_int").unwrap()),
        IntTy::I128 => Exp::qvar(QName::from_string("Int128.to_int").unwrap()),
    }
}

pub(crate) fn uint_to_int(uty: &UintTy) -> Exp {
    match uty {
        UintTy::Usize => Exp::qvar(QName::from_string("UIntSize.to_int").unwrap()),
        UintTy::U8 => Exp::qvar(QName::from_string("UInt8.to_int").unwrap()),
        UintTy::U16 => Exp::qvar(QName::from_string("UInt16.to_int").unwrap()),
        UintTy::U32 => Exp::qvar(QName::from_string("UInt32.to_int").unwrap()),
        UintTy::U64 => Exp::qvar(QName::from_string("UInt64.to_int").unwrap()),
        UintTy::U128 => Exp::qvar(QName::from_string("UInt128.to_int").unwrap()),
    }
}
