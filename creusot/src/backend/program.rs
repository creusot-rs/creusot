use super::{
    clone_map::PreludeModule,
    dependency::ExtendedId,
    place::rplace_to_expr,
    signature::{sig_to_why3, signature_of},
    term::lower_pure,
    ty::{destructor, int_ty},
    CloneSummary, GraphDepth, NameSupply, Namer, TransId, Why3Generator,
};
use crate::{
    backend::{
        closure_generic_decls, optimization,
        optimization::infer_proph_invariants,
        place,
        ty::{self, translate_closure_ty, translate_ty},
        wto::weak_topological_order,
    },
    ctx::{BodyId, Dependencies, TranslationCtx},
    fmir::{Body, BorrowKind, Operand},
    translation::fmir::{self, Block, Branches, LocalDecls, Place, RValue, Statement, Terminator},
    util::{self, module_name},
};

use petgraph::graphmap::DiGraphMap;
use rustc_hir::{def_id::DefId, Safety};
use rustc_middle::{
    mir::{self, BasicBlock, BinOp, ProjectionElem, UnOp, START_BLOCK},
    ty::{AdtDef, GenericArgsRef, Ty, TyKind},
};
use rustc_span::{Span, Symbol, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{FloatTy, IntTy, UintTy};
use why3::{
    coma::{self, Arg, Defn, Expr, Param, Term},
    declaration::{Attribute, Contract, Decl, Module, Signature},
    exp::{Binder, Constant, Exp},
    ty::Type,
    Ident, QName,
};

fn closure_ty<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Module {
    let mut names = Dependencies::new(ctx.tcx, [def_id]);
    let mut decls = Vec::new();

    let ty = ctx.type_of(def_id).instantiate_identity();
    let TyKind::Closure(_, subst) = ty.kind() else { unreachable!() };
    names.insert_hidden_type(ctx.type_of(def_id).instantiate_identity());
    let env_ty = Decl::TyDecl(translate_closure_ty(ctx, &mut names, def_id, subst));

    let d = destructor(ctx, &mut names, def_id, ty, 0u32.into());

    let (clones, _) = names.provide_deps(ctx, GraphDepth::Deep);
    decls.extend(
        // Definitely a hack but good enough for the moment
        clones.into_iter().filter(|d| matches!(d, Decl::UseDecl(_))),
    );
    decls.push(env_ty);

    decls.push(d);

    Module { name: format!("{}_Type", module_name(ctx.tcx, def_id)).into(), decls }
}

pub(crate) fn closure_aux_defs<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) {
    // COMPLETE HACK. This should be properly cleaned up
    let contract = ctx.closure_contract(def_id).clone();

    // HACK RESOLVE
    let mut names = Dependencies::new(ctx.tcx, [def_id]);
    sig_to_why3(ctx, &mut names, &contract.resolve.0, def_id);
    lower_pure(ctx, &mut names, &contract.resolve.1);

    let (_, deps) = names.provide_deps(ctx, GraphDepth::Shallow);
    ctx.dependencies.insert(TransId::Hacked(ExtendedId::Resolve, def_id), deps);

    // HACK PRECOND
    let mut names = Dependencies::new(ctx.tcx, [def_id]);
    sig_to_why3(ctx, &mut names, &contract.precond.0, def_id);
    lower_pure(ctx, &mut names, &contract.precond.1);

    let (_, deps) = names.provide_deps(ctx, GraphDepth::Shallow);
    ctx.dependencies.insert(TransId::Hacked(ExtendedId::Precondition, def_id), deps);

    // HACK POST ONCE
    if let Some((sig, term)) = contract.postcond_once {
        let mut names = Dependencies::new(ctx.tcx, [def_id]);
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.provide_deps(ctx, GraphDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(ExtendedId::PostconditionOnce, def_id), deps);
    }

    // HACK POST MUT
    if let Some((sig, term)) = contract.postcond_mut {
        let mut names = Dependencies::new(ctx.tcx, [def_id]);
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.provide_deps(ctx, GraphDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(ExtendedId::PostconditionMut, def_id), deps);
    }
    // HACK POST
    if let Some((sig, term)) = contract.postcond {
        let mut names = Dependencies::new(ctx.tcx, [def_id]);
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.provide_deps(ctx, GraphDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(ExtendedId::Postcondition, def_id), deps);
    }
    // HACK UNNEst
    if let Some((sig, term)) = contract.unnest {
        let mut names = Dependencies::new(ctx.tcx, [def_id]);
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.provide_deps(ctx, GraphDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(ExtendedId::Unnest, def_id), deps);
    } // END COMPLETE HACK
      // decls.extend(contract);
      // decls
    for (ix, (sig, term)) in contract.accessors.into_iter().enumerate() {
        let mut names = Dependencies::new(ctx.tcx, [def_id]);
        sig_to_why3(ctx, &mut names, &sig, def_id);
        lower_pure(ctx, &mut names, &term);

        let (_, deps) = names.provide_deps(ctx, GraphDepth::Shallow);
        ctx.dependencies.insert(TransId::Hacked(ExtendedId::Accessor(ix as u8), def_id), deps);
    }
}

pub(crate) fn translate_closure<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (CloneSummary<'tcx>, Module, Option<Module>) {
    assert!(ctx.is_closure_like(def_id));
    let (summary, func) = translate_function(ctx, def_id);
    (summary, closure_ty(ctx, def_id), func)
}

pub(crate) fn translate_function<'tcx, 'sess>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (CloneSummary<'tcx>, Option<Module>) {
    let tcx = ctx.tcx;
    let mut names = Dependencies::new(tcx, [def_id]);

    let Some((body_id, promoteds)) = collect_body_ids(ctx, def_id) else {
        let (_, clones) = names.provide_deps(ctx, GraphDepth::Deep);
        return (clones, None);
    };
    let body = Decl::Coma(to_why(ctx, &mut names, body_id));

    if ctx.tcx.is_closure_like(def_id) {
        closure_aux_defs(ctx, def_id)
    };

    let promoteds = promoteds
        .iter()
        .map(|body_id| Decl::Coma(to_why(ctx, &mut names, *body_id)))
        .collect::<Vec<_>>();

    let (clones, summary) = names.provide_deps(ctx, GraphDepth::Deep);

    let decls = closure_generic_decls(ctx.tcx, def_id)
        .chain(clones)
        .chain(promoteds)
        .chain(std::iter::once(body))
        .collect();

    let name = Ident::build(&module_name(ctx.tcx, def_id).to_string());
    (summary, Some(Module { name, decls }))
}

/// If `def_id`'s body should be translated, returns:
/// - The `BodyId` corresponding to `def_id`
/// - The `BodyId`s of promoted items
fn collect_body_ids<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Option<(BodyId, Vec<BodyId>)> {
    let body_id =
        if def_id.is_local() && util::has_body(ctx, def_id) && !util::is_trusted(ctx.tcx, def_id) {
            BodyId::new(def_id.expect_local(), None)
        } else {
            return None;
        };

    let tcx = ctx.tcx;
    let promoted = ctx
        .body_with_facts(def_id.expect_local())
        .promoted
        .iter_enumerated()
        .map(|(p, p_body)| (p, p_body.return_ty()))
        .filter_map(|(p, p_ty)| {
            if util::snapshot_closure_id(tcx, p_ty).is_none() {
                Some(BodyId::new(def_id.expect_local(), Some(p)))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    Some((body_id, promoted))
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

    body = sig.contract.requires.into_iter().fold(body, |acc, ensures| {
        Expr::Assert(
            Box::new(Term::Attr(Attribute::Attr(format!("expl:precondition")), Box::new(ensures))),
            Box::new(acc),
        )
    });

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

// TODO: move to a more "central" location
pub(crate) fn node_graph(x: &Body) -> petgraph::graphmap::DiGraphMap<BasicBlock, ()> {
    let mut graph = DiGraphMap::default();
    for (bb, data) in &x.blocks {
        graph.add_node(*bb);
        for tgt in data.terminator.targets() {
            graph.add_edge(*bb, tgt, ());
        }
    }

    graph
}

pub fn to_why<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    body_id: BodyId,
) -> coma::Defn {
    let mut body = ctx.fmir_body(body_id).clone();

    let usage = optimization::gather_usage(&body);
    optimization::simplify_fmir(usage, &mut body);

    let wto = weak_topological_order(&node_graph(&body), START_BLOCK);
    infer_proph_invariants(ctx, body_id.def_id(), &mut body);

    let blocks: Vec<Defn> =
        wto.into_iter().map(|c| component_to_defn(&mut body, ctx, names, c)).collect();
    let ret = body.locals.first().map(|(_, decl)| decl.clone());

    let vars: Vec<_> = body
        .locals
        .into_iter()
        .map(|(id, decl)| {
            let ty = ty::translate_ty(ctx, names, decl.span, decl.ty);

            let init = if decl.arg {
                Exp::var(Ident::build(id.as_str()))
            } else {
                names.import_prelude_module(PreludeModule::Intrinsic);
                Exp::var("any_l").app_to(Exp::Tuple(Vec::new()))
            };
            coma::Var(Ident::build(id.as_str()), ty.clone(), init, coma::IsRef::Ref)
        })
        .collect();

    let sig = if body_id.promoted.is_none() {
        signature_of(ctx, names, body_id.def_id())
    } else {
        let ret = ret.unwrap();
        Signature {
            name: format!("promoted{}", body_id.promoted.unwrap().as_usize()).into(),
            trigger: None,
            attrs: vec![],
            retty: Some(ty::translate_ty(ctx, names, ret.span, ret.ty)),
            args: vec![],
            contract: Contract::default(),
        }
    };
    let mut body = Expr::Defn(Box::new(Expr::Symbol("bb0".into())), true, blocks);

    let mut postcond = Expr::Symbol("return".into()).app(vec![Arg::Term(Exp::var("result"))]);

    if body_id.promoted.is_none() && !util::is_ghost_closure(ctx.tcx, body_id.def_id()) {
        postcond = Expr::BlackBox(Box::new(postcond));
    }
    postcond = sig.contract.ensures.into_iter().fold(postcond, |acc, ensures| {
        Expr::Assert(
            Box::new(Exp::Attr(Attribute::Attr("expl:postcondition".into()), Box::new(ensures))),
            Box::new(acc),
        )
    });

    if body_id.promoted.is_none() && !util::is_ghost_closure(ctx.tcx, body_id.def_id()) {
        body = Expr::BlackBox(Box::new(body))
    };

    body = Expr::Let(Box::new(body), vars);

    body = Expr::Defn(
        Box::new(body),
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
    coma::Defn { name: sig.name, writes: Vec::new(), params, body }
}

use super::wto::Component;

fn component_to_defn<'tcx, N: Namer<'tcx>>(
    body: &mut Body<'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    c: Component<BasicBlock>,
) -> coma::Defn {
    let mut lower =
        LoweringState { ctx, names, locals: &body.locals, name_supply: Default::default() };
    let (head, tl) = match c {
        Component::Vertex(v) => {
            let block = body.blocks.remove(&v).unwrap();
            return block.to_why(&mut lower, v);
        }
        Component::Component(v, tls) => (v, tls),
    };

    let block = body.blocks.remove(&head).unwrap();
    let mut block = block.to_why(&mut lower, head);

    let defns = tl.into_iter().map(|id| component_to_defn(body, ctx, names, id)).collect();

    if !block.body.is_guarded() {
        block.body = Expr::BlackBox(Box::new(block.body));
    }

    let inner = Expr::Defn(Box::new(block.body), true, defns);
    block.body = Expr::Defn(
        Box::new(Expr::Symbol(block.name.clone().into())),
        true,
        vec![Defn::simple(block.name.clone(), inner)],
    );
    block
}

pub(crate) struct LoweringState<'a, 'tcx, N: Namer<'tcx>> {
    pub(super) ctx: &'a mut Why3Generator<'tcx>,
    pub(super) names: &'a mut N,
    pub(super) locals: &'a LocalDecls<'tcx>,
    pub(super) name_supply: NameSupply,
}

impl<'a, 'tcx, N: Namer<'tcx>> LoweringState<'a, 'tcx, N> {
    pub(super) fn ty(&mut self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, DUMMY_SP, ty)
    }

    fn assignment(&mut self, lhs: &Place<'tcx>, rhs: Term) -> Vec<IntermediateStmt> {
        place::create_assign_inner(self, lhs, rhs, DUMMY_SP)
    }

    fn reset_names(&mut self) {}

    pub(super) fn fresh_from(&mut self, base: impl AsRef<str>) -> Ident {
        self.name_supply.freshen(Symbol::intern(base.as_ref())).to_string().into()
    }
}

impl<'tcx> Operand<'tcx> {
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> Exp {
        match self {
            Operand::Move(pl) => pl.as_rplace(lower, istmts),
            Operand::Copy(pl) => pl.as_rplace(lower, istmts),
            Operand::Constant(c) => lower_pure(lower.ctx, lower.names, &c),
            Operand::Promoted(pid, ty) => {
                let promoted = Expr::Symbol(
                    QName::from_string(&format!("promoted{}", pid.as_usize())).unwrap(),
                );
                let var: Ident = Ident::build(&format!("pr{}", pid.as_usize()));
                istmts.push(IntermediateStmt::call(var.clone(), lower.ty(ty), promoted, vec![]));

                Exp::var(var)
            }
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
        lower: &mut LoweringState<'_, 'tcx, N>,
        ty: Ty<'tcx>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> Exp {
        let e = match self {
            RValue::Operand(op) => op.to_why(lower, istmts),
            RValue::BinOp(BinOp::BitAnd, l, r) if l.ty(lower.ctx.tcx, lower.locals).is_bool() => {
                l.to_why(lower, istmts).lazy_and(r.to_why(lower, istmts))
            }
            RValue::BinOp(BinOp::Eq, l, r) if l.ty(lower.ctx.tcx, lower.locals).is_bool() => {
                lower.names.import_prelude_module(PreludeModule::Bool);

                Exp::qvar(QName::from_string("Bool.eq").unwrap())
                    .app(vec![l.to_why(lower, istmts), r.to_why(lower, istmts)])
            }
            RValue::BinOp(BinOp::Ne, l, r) if l.ty(lower.ctx.tcx, lower.locals).is_bool() => {
                lower.names.import_prelude_module(PreludeModule::Bool);

                Exp::qvar(QName::from_string("Bool.ne").unwrap())
                    .app(vec![l.to_why(lower, istmts), r.to_why(lower, istmts)])
            }
            RValue::BinOp(op, l, r) => {
                let l_ty = l.ty(lower.ctx.tcx, lower.locals);
                let fname = binop_to_binop(lower.names, l_ty, op);
                let call = coma::Expr::Symbol(fname);
                let args =
                    vec![Arg::Term(l.to_why(lower, istmts)), Arg::Term(r.to_why(lower, istmts))];
                istmts.extend([IntermediateStmt::call("_ret'".into(), lower.ty(ty), call, args)]);
                // let ty = l.ty(lower.ctx.tcx, locals);
                // // Hack
                // translate_ty(ctx, names, DUMMY_SP, ty);

                Exp::var("_ret'")
                // let op_ty = l.ty(ctx.tcx, locals);
                // // Hack
                // translate_ty(ctx, names, DUMMY_SP, op_ty);
            }
            RValue::UnaryOp(UnOp::Not, arg) => arg.to_why(lower, istmts).not(),
            RValue::UnaryOp(UnOp::Neg, arg) => {
                let prelude: PreludeModule = match ty.kind() {
                    TyKind::Int(ity) => int_to_prelude(*ity),
                    TyKind::Uint(uty) => uint_to_prelude(*uty),
                    TyKind::Float(FloatTy::F32) => PreludeModule::Float32,
                    TyKind::Float(FloatTy::F64) => PreludeModule::Float64,
                    TyKind::Bool => PreludeModule::Bool,
                    _ => unreachable!("non-primitive type for negation {ty:?}"),
                };

                lower.names.import_prelude_module(prelude);
                let mut module = prelude.qname();
                module = module.without_search_path();
                module.push_ident("neg");

                let id: Ident = "_ret".into();
                let ty = lower.ty(ty);
                let arg = arg.to_why(lower, istmts);
                istmts.push(IntermediateStmt::call(
                    id.clone(),
                    ty,
                    Expr::Symbol(module),
                    vec![Arg::Term(arg)],
                ));

                Exp::var(id)
            }
            RValue::Constructor(id, subst, args) => {
                let args = args.into_iter().map(|a| a.to_why(lower, istmts)).collect();

                let ctor = lower.names.constructor(id, subst);
                Exp::Constructor { ctor, args }
            }
            RValue::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(lower, istmts)).collect())
            }
            RValue::Cast(e, source, target) => {
                let to_int = match source.kind() {
                    TyKind::Int(ity) => {
                        lower.names.import_prelude_module(int_to_prelude(*ity));
                        int_to_int(ity)
                    }
                    TyKind::Uint(uty) => {
                        lower.names.import_prelude_module(uint_to_prelude(*uty));
                        uint_to_int(uty)
                    }
                    TyKind::Bool => {
                        lower.names.import_prelude_module(PreludeModule::Bool);
                        Exp::qvar(QName::from_string("Bool.to_int").unwrap())
                    }
                    _ => lower
                        .ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                let from_int = match target.kind() {
                    TyKind::Int(ity) => int_from_int(ity),
                    TyKind::Uint(uty) => uint_from_int(uty),
                    TyKind::Char => {
                        lower.names.import_prelude_module(PreludeModule::Char);
                        QName::from_string("Char.chr").unwrap()
                    }
                    _ => lower
                        .ctx
                        .crash_and_error(DUMMY_SP, "Non integral casts are currently unsupported"),
                };

                let int = to_int.app_to(e.to_why(lower, istmts));

                istmts.push(IntermediateStmt::call(
                    "_res".into(),
                    lower.ty(ty),
                    Expr::Symbol(from_int),
                    vec![Arg::Term(int)],
                ));

                Exp::var("_res")
            }
            RValue::Len(pl) => {
                let len_call = Exp::qvar(QName::from_string("Slice.length").unwrap())
                    .app_to(pl.to_why(lower, istmts));
                len_call
            }
            RValue::Array(fields) => {
                let id = Ident::build("__arr_temp");
                let ty = lower.ty(ty);

                let len = fields.len();

                let arr_var = Exp::var(id.clone());
                let arr_elts =
                    Exp::RecField { record: Box::new(arr_var.clone()), label: "elts".into() };

                istmts.push(IntermediateStmt::Any(id.clone(), ty.clone()));
                let mut assumptions = fields
                    .into_iter()
                    .enumerate()
                    .map(|(ix, f)| {
                        Exp::qvar(QName::from_string("Seq.get").unwrap())
                            .app(vec![
                                arr_elts.clone(),
                                Exp::Const(Constant::Int(ix as i128, None)),
                            ])
                            .eq(f.to_why(lower, istmts))
                    })
                    .chain([Exp::qvar(QName::from_string("Seq.length").unwrap())
                        .app_to(arr_elts.clone())
                        .eq(Exp::Const(Constant::Int(len as i128, None)))])
                    .reduce(Exp::log_and)
                    .expect("array literal missing assumption");
                assumptions.reassociate();

                istmts.push(IntermediateStmt::Assume(assumptions));
                Exp::var(id)
            }
            RValue::Repeat(e, len) => {
                let slice_create = QName::from_string("Slice.create").unwrap();
                let param_ty = lower.ty(e.ty(lower.ctx.tcx, lower.locals));
                let args = vec![
                    Arg::Ty(param_ty),
                    Arg::Term(len.to_why(lower, istmts)),
                    Arg::Term(Exp::Abs(
                        vec![Binder::wild(int_ty(lower.ctx, lower.names))],
                        Box::new(e.to_why(lower, istmts)),
                    )),
                ];

                istmts.push(IntermediateStmt::call(
                    "_res".into(),
                    lower.ty(ty),
                    Expr::Symbol(slice_create),
                    args,
                ));

                Exp::var("_res")
            }
            RValue::Ghost(t) => lower_pure(lower.ctx, lower.names, &t),
            RValue::Borrow(_, _) | RValue::UnaryOp(UnOp::PtrMetadata, _) => todo!(),
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

// fn mk_constructor() -> Exp {

// }

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
                            *bb = to
                        }
                    }
                }
                Branches::Uint(brs, def) => {
                    if *def == from {
                        *def = to
                    };
                    for (_, bb) in brs {
                        if *bb == from {
                            *bb = to
                        }
                    }
                }
                Branches::Constructor(_, _, brs, def) => {
                    if *def == Some(from) {
                        *def = Some(to)
                    };
                    for (_, bb) in brs {
                        if *bb == from {
                            *bb = to
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

    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
    ) -> (Vec<IntermediateStmt>, coma::Expr) {
        use coma::*;
        let mut istmts = vec![];
        match self {
            Terminator::Goto(bb) => (istmts, Expr::Symbol(format!("bb{}", bb.as_usize()).into())),
            Terminator::Switch(switch, branches) => {
                let discr = switch.to_why(lower, &mut istmts);
                (istmts, branches.to_why(lower.ctx, lower.names, discr))
            }
            Terminator::Return => {
                (istmts, Expr::Symbol("return".into()).app(vec![Arg::Term(Exp::var("_0"))]))
            }
            Terminator::Abort(span) => {
                let mut exp = Exp::mk_false();
                if let Some(attr) = lower.names.span(span) {
                    exp = exp.with_attr(attr);
                };
                (istmts, Expr::Assert(Box::new(exp), Box::new(Expr::Any)))
            }
        }
    }
}

impl<'tcx> Branches<'tcx> {
    fn to_why<N: Namer<'tcx>>(
        self,
        _ctx: &mut Why3Generator<'tcx>,
        names: &mut N,
        discr: Exp,
    ) -> coma::Expr {
        match self {
            Branches::Int(brs, def) => {
                let mut brs = mk_switch_branches(
                    discr,
                    brs.into_iter().map(|(val, tgt)| (Exp::int(val), mk_goto(tgt))).collect(),
                );

                brs.push(Defn::simple("default", Expr::BlackBox(Box::new(mk_goto(def)))));
                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
            Branches::Uint(brs, def) => {
                let mut brs = mk_switch_branches(
                    discr,
                    brs.into_iter().map(|(val, tgt)| (Exp::uint(val), mk_goto(tgt))).collect(),
                );

                brs.push(Defn::simple("default", Expr::BlackBox(Box::new(mk_goto(def)))));
                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
            Branches::Constructor(adt, _substs, vars, def) => {
                let brs = mk_adt_switch(
                    _ctx,
                    names,
                    adt,
                    _substs,
                    discr,
                    vars.into_iter().map(|(var, bb)| (var, mk_goto(bb))).collect(),
                    def.map(mk_goto),
                );

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

fn mk_adt_switch<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    adt: AdtDef<'tcx>,
    subst: GenericArgsRef<'tcx>,
    discr: Exp,
    mut brch: Vec<(VariantIdx, coma::Expr)>,
    default: Option<coma::Expr>,
) -> Vec<coma::Defn> {
    let mut out = Vec::new();

    let mut branches = Vec::new();
    for ix in 0..adt.variants().len() {
        if let Some((vix, _)) = brch.get(0)
            && *vix == VariantIdx::from(ix)
        {
            branches.push(brch.remove(0));
        } else {
            branches.push((VariantIdx::from(ix), default.clone().unwrap()))
        }
    }

    let brch = branches;

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
            coma::Defn { name: format!("br{c}").into(), body: filter, params, writes: Vec::new() };
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

        let branch = coma::Defn::simple(format!("br{ix}"), filter);
        out.push(branch)
    }
    out
}

impl<'tcx> Block<'tcx> {
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        id: BasicBlock,
    ) -> coma::Defn {
        let (istmts, terminator) = self.terminator.to_why(lower);

        let mut statements = vec![];

        for (ix, s) in self.stmts.into_iter().enumerate() {
            lower.reset_names();
            let stmt = s.to_why(lower);

            let body = assemble_intermediates(
                stmt.into_iter(),
                Expr::Symbol(format!("s{}", ix + 1).into()),
            );
            statements.push(coma::Defn::simple(format!("s{}", ix), body));
        }

        let body = assemble_intermediates(istmts.into_iter(), terminator);
        statements.push(coma::Defn::simple(format!("s{}", statements.len()), body));

        let mut body = Expr::Symbol("s0".into());
        if !self.invariants.is_empty() {
            body = Expr::BlackBox(Box::new(body));
        }

        for i in self.invariants {
            body = Expr::Assert(
                Box::new(Term::Attr(
                    Attribute::Attr(format!("expl:loop invariant")),
                    Box::new(lower_pure(lower.ctx, lower.names, &i)),
                )),
                Box::new(body),
            );
        }

        body = body.where_(statements);

        coma::Defn::simple(format!("bb{}", id.as_usize()), body)
    }
}

fn assemble_intermediates<I>(istmts: I, exp: Expr) -> Expr
where
    I: IntoIterator<Item = IntermediateStmt>,
    I: DoubleEndedIterator<Item = IntermediateStmt>,
{
    istmts.rfold(exp, |tail, stmt| match stmt {
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
                body: Expr::BlackBox(Box::new(tail)),
            }],
        ),
    })
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn as_rplace<N: Namer<'tcx>>(
        &self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> why3::Exp {
        let (e, t) = rplace_to_expr(lower, self.local, &self.projection);
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

#[derive(Debug)]
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
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
    ) -> Vec<IntermediateStmt> {
        match self {
            Statement::Assignment(lhs, RValue::Borrow(BorrowKind::Mut, rhs), _span) => {
                let borrow_mut =
                    coma::Expr::Symbol(QName::from_string("Borrow.borrow_mut").unwrap());

                let mut istmts = Vec::new();
                let args = vec![
                    Arg::Ty(lower.ty(rhs.ty(lower.ctx.tcx, lower.locals))),
                    Arg::Term(rhs.as_rplace(lower, &mut istmts)),
                ];
                let reassign = lhs.as_rplace(lower, &mut istmts).field("final");

                let ty = lhs.ty(lower.ctx.tcx, lower.locals);

                let borrow_call =
                    IntermediateStmt::call("_ret'".into(), lower.ty(ty), borrow_mut, args);

                istmts.extend([borrow_call]);
                istmts.extend(lower.assignment(&lhs, Exp::var("_ret'")));
                istmts.extend(lower.assignment(&rhs, reassign));

                istmts
            }
            Statement::Assignment(
                lhs,
                RValue::Borrow(BorrowKind::Final(deref_index), rhs),
                _span,
            ) => {
                let mut istmts = Vec::new();

                let original_borrow = Place {
                    local: rhs.local.clone(),
                    projection: rhs.projection[..deref_index].to_vec(),
                }
                .as_rplace(lower, &mut istmts);

                let ty = lhs.ty(lower.ctx.tcx, lower.locals);

                let borrow_id =
                    borrow_generated_id(original_borrow, &rhs.projection[deref_index + 1..]);
                let reassign = lhs.as_rplace(lower, &mut istmts).field("final");

                let assign1 = { lower.assignment(&lhs, Exp::var("_ret'")) };

                let assign2 = { lower.assignment(&rhs, reassign) };

                let borrow_mut =
                    coma::Expr::Symbol(QName::from_string("Borrow.borrow_final").unwrap());

                let args = vec![
                    Arg::Ty(lower.ty(rhs.ty(lower.ctx.tcx, lower.locals))),
                    Arg::Term(rhs.as_rplace(lower, &mut istmts)),
                    Arg::Term(borrow_id),
                ];

                let borrow_call =
                    IntermediateStmt::call("_ret'".into(), lower.ty(ty), borrow_mut, args);

                istmts.extend([borrow_call]);
                istmts.extend(assign1);
                istmts.extend(assign2);
                istmts
            }
            Statement::Assignment(lhs, e, span) => {
                let mut istmts = Vec::new();

                let mut invalid = Vec::new();
                e.invalidated_places(&mut invalid);

                let rhs = e.to_why(lower, lhs.ty(lower.ctx.tcx, lower.locals), &mut istmts);
                let assign = lower.assignment(&lhs, rhs);
                istmts.extend(assign);
                invalidate_places(lower, span, invalid, &mut istmts);

                istmts
            }
            Statement::Call(dest, fun_id, subst, args, _) => {
                let mut istmts = Vec::new();

                let (fun_exp, args) = func_call_to_why3(lower, fun_id, subst, args, &mut istmts);
                let ty = dest.ty(lower.ctx.tcx, lower.locals);
                let ty = lower.ty(ty);
                let assign = lower.assignment(&dest, Exp::var("_ret'"));

                istmts.extend([IntermediateStmt::call("_ret'".into(), ty, fun_exp, args)]);
                istmts.extend(assign);
                istmts
            }
            Statement::Resolve(id, subst, pl) => {
                lower.ctx.translate(id);
                let mut istmts = Vec::new();

                let rp = Exp::qvar(lower.names.value(id, subst));

                let assume = rp.app_to(pl.as_rplace(lower, &mut istmts));

                istmts.extend([IntermediateStmt::Assume(assume)]);
                istmts
            }
            Statement::Assertion { cond, msg } => {
                vec![IntermediateStmt::Assert(Exp::Attr(
                    Attribute::Attr(format!("expl:{msg}")),
                    Box::new(lower_pure(lower.ctx, lower.names, &cond)),
                ))]
            }
            Statement::AssumeBorrowInv(pl) => {
                let inv_fun = Exp::qvar(
                    lower
                        .names
                        .ty_inv(pl.ty(lower.ctx.tcx, lower.locals).builtin_deref(false).unwrap()),
                );
                let mut istmts = Vec::new();

                let arg = pl.as_rplace(lower, &mut istmts).field("final");

                istmts.extend(vec![IntermediateStmt::Assume(inv_fun.app_to(arg))]);
                istmts
            }
            Statement::AssertTyInv(pl) => {
                let inv_fun = Exp::qvar(lower.names.ty_inv(pl.ty(lower.ctx.tcx, lower.locals)));
                let mut istmts = Vec::new();

                let arg = pl.as_rplace(lower, &mut istmts);
                let exp = Exp::Attr(
                    Attribute::Attr(format!("expl:type invariant")),
                    Box::new(inv_fun.app_to(arg)),
                );

                istmts.extend(vec![IntermediateStmt::Assert(exp)]);
                istmts
            }
        }
    }
}

fn invalidate_places<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    _span: Span,
    invalid: Vec<Place<'tcx>>,
    out: &mut Vec<IntermediateStmt>,
) {
    // any (x -> lhs = x )
    for pl in invalid {
        let ty = pl.ty(lower.ctx.tcx, lower.locals);
        let ty = lower.ty(ty);

        let assign = lower.assignment(&pl, Exp::var("_any"));
        out.push(IntermediateStmt::Any("_any".into(), ty));
        out.extend(assign);
    }
}

fn func_call_to_why3<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
    mut args: Vec<Operand<'tcx>>,
    istmts: &mut Vec<IntermediateStmt>,
) -> (coma::Expr, Vec<coma::Arg>) {
    // TODO(xavier): Perform this simplification earlier
    // Eliminate "rust-call" ABI
    let args: Vec<_> = if lower.ctx.is_closure_like(id) {
        assert!(args.len() == 2, "closures should only have two arguments (env, args)");

        let real_sig = lower.ctx.signature_unclosure(subst.as_closure().sig(), Safety::Safe);

        let Operand::Move(pl) = args.remove(1) else { panic!() };
        let mut args = vec![coma::Arg::Term(args.remove(0).to_why(lower, istmts))];
        for (ix, inp) in real_sig.inputs().skip_binder().iter().enumerate() {
            let mut arg = pl.clone();
            arg.projection.push(ProjectionElem::Field(ix.into(), *inp));
            args.push(coma::Arg::Term(Operand::Move(arg).to_why(lower, istmts)));
        }
        args
    } else {
        args.into_iter().map(|a| a.to_why(lower, istmts)).map(|a| coma::Arg::Term(a)).collect()
    };

    let fname = lower.names.value(id, subst);

    (coma::Expr::Symbol(fname), args)
}

pub(crate) fn binop_to_binop<'tcx, N: Namer<'tcx>>(names: &mut N, ty: Ty, op: mir::BinOp) -> QName {
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

    use BinOp::*;
    match op {
        Add => module.push_ident("add"),
        AddUnchecked => module.push_ident("add"),
        Sub => module.push_ident("sub"),
        SubUnchecked => module.push_ident("sub"),
        Mul => module.push_ident("mul"),
        MulUnchecked => module.push_ident("mul"),
        Div => module.push_ident("div"),
        Rem => module.push_ident("rem"),
        BitXor => module.push_ident("bw_xor"),
        BitAnd => module.push_ident("bw_and"),
        BitOr => module.push_ident("bw_or"),
        Shl => module.push_ident("shl"),
        ShlUnchecked => module.push_ident("shl"),
        Shr => module.push_ident("shr"),
        ShrUnchecked => module.push_ident("shr"),
        Eq => module.push_ident("eq"),
        Lt => module.push_ident("lt"),
        Le => module.push_ident("le"),
        Ne => module.push_ident("ne"),
        Ge => module.push_ident("ge"),
        Gt => module.push_ident("gt"),
        Cmp | AddWithOverflow | SubWithOverflow | MulWithOverflow => todo!(),
        Offset => unimplemented!("pointer offsets are unsupported"),
    };

    module = module.without_search_path();
    module
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

pub(crate) fn int_from_int(ity: &IntTy) -> QName {
    match ity {
        IntTy::Isize => QName::from_string("IntSize.of_int").unwrap(),
        IntTy::I8 => QName::from_string("Int8.of_int").unwrap(),
        IntTy::I16 => QName::from_string("Int16.of_int").unwrap(),
        IntTy::I32 => QName::from_string("Int32.of_int").unwrap(),
        IntTy::I64 => QName::from_string("Int64.of_int").unwrap(),
        IntTy::I128 => QName::from_string("Int128.of_int").unwrap(),
    }
}

pub(crate) fn uint_from_int(uty: &UintTy) -> QName {
    match uty {
        UintTy::Usize => QName::from_string("UIntSize.of_int").unwrap(),
        UintTy::U8 => QName::from_string("UInt8.of_int").unwrap(),
        UintTy::U16 => QName::from_string("UInt16.of_int").unwrap(),
        UintTy::U32 => QName::from_string("UInt32.of_int").unwrap(),
        UintTy::U64 => QName::from_string("UInt64.of_int").unwrap(),
        UintTy::U128 => QName::from_string("UInt128.of_int").unwrap(),
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
