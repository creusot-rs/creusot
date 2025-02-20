use crate::{
    backend::{
        clone_map::PreludeModule,
        dependency::Dependency,
        is_trusted_function,
        optimization::{self, infer_proph_invariants},
        place::{self, rplace_to_expr},
        signature::signature_of,
        term::{lower_pat, lower_pure},
        ty::{
            constructor, floatty_to_prelude, int_ty, ity_to_prelude, translate_ty, uty_to_prelude,
        },
        wto::{weak_topological_order, Component},
        NameSupply, Namer, Why3Generator,
    },
    contracts_items::is_ghost_closure,
    ctx::{BodyId, Dependencies},
    fmir::{self, Body, BorrowKind, Operand, TrivialInv},
    naming::ident_of,
    pearlite::{self, PointerKind},
    translated_item::FileModule,
    translation::fmir::{Block, Branches, LocalDecls, Place, RValue, Statement, Terminator},
};

use petgraph::graphmap::DiGraphMap;
use rustc_ast::Mutability;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    Safety,
};
use rustc_middle::{
    mir::{self, tcx::PlaceTy, BasicBlock, BinOp, ProjectionElem, UnOp, START_BLOCK},
    ty::{AdtDef, GenericArgsRef, Ty, TyCtxt, TyKind},
};
use rustc_span::{Symbol, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{IntTy, UintTy};
use std::{cell::RefCell, fmt::Debug};
use why3::{
    coma::{self, Arg, Defn, Expr, Param, Term},
    declaration::{
        Attribute, Condition, Contract, Decl, Meta, MetaArg, MetaIdent, Module, Signature,
    },
    exp::{Binder, Constant, Exp, Pattern},
    ty::Type,
    Ident, QName,
};

pub(crate) fn translate_function<'tcx, 'sess>(
    ctx: &Why3Generator<'tcx>,
    def_id: DefId,
) -> Option<FileModule> {
    let mut names = Dependencies::new(ctx, def_id);

    if !def_id.is_local() || !ctx.has_body(def_id) || is_trusted_function(ctx.tcx, def_id) {
        return None;
    }

    let name = names.item(names.self_id, names.self_subst).as_ident();
    let body = Decl::Coma(to_why(ctx, &mut names, name, BodyId::new(def_id.expect_local(), None)));

    let mut decls = names.provide_deps(ctx);
    decls.push(Decl::Meta(Meta {
        name: MetaIdent::String("compute_max_steps".into()),
        args: vec![MetaArg::Integer(1_000_000)],
    }));
    decls.push(body);

    let attrs = Vec::from_iter(ctx.span_attr(ctx.def_span(def_id)));
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Some(FileModule { path, modl: Module { name, decls, attrs, meta } })
}

pub fn val<'tcx>(_: &Why3Generator<'tcx>, sig: Signature) -> Decl {
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
    let requires = sig.contract.requires.into_iter().map(Condition::labelled_exp);
    let body = requires.rfold(Expr::Any, |acc, cond| Expr::Assert(Box::new(cond), Box::new(acc)));

    let mut postcond = Expr::Symbol("return".into()).app(vec![Arg::Term(Exp::var("result"))]);
    postcond = Expr::BlackBox(Box::new(postcond));
    let ensures = sig.contract.ensures.into_iter().map(Condition::unlabelled_exp);
    postcond = ensures.rfold(postcond, |acc, cond| Expr::Assert(Box::new(cond), Box::new(acc)));

    let body = Expr::Defn(
        Box::new(body),
        false,
        vec![Defn {
            name: "return".into(),
            writes: Vec::new(),
            attrs: vec![],

            params: vec![Param::Term("result".into(), sig.retty.clone().unwrap())],
            body: postcond,
        }],
    );
    why3::declaration::Decl::Coma(Defn {
        name: sig.name,
        writes: Vec::new(),
        attrs: vec![],
        params,
        body,
    })
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
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    body_id: BodyId,
) -> coma::Defn {
    let mut body = ctx.fmir_body(body_id).clone();

    let usage = optimization::gather_usage(&body);
    optimization::simplify_fmir(usage, &mut body);

    let wto = weak_topological_order(&node_graph(&body), START_BLOCK);
    infer_proph_invariants(ctx, &mut body);

    let blocks: Vec<Defn> = wto
        .into_iter()
        .map(|c| component_to_defn(&mut body, ctx, names, body_id.def_id, c))
        .collect();
    let ret = body.locals.first().map(|(_, decl)| decl.clone());

    let vars: Vec<_> = body
        .locals
        .into_iter()
        .map(|(id, decl)| {
            let ty = translate_ty(ctx, names, decl.span, decl.ty);

            let init = if decl.arg {
                Exp::var(Ident::build(id.as_str()))
            } else {
                Exp::qvar(names.from_prelude(PreludeModule::Intrinsic, "any_l"))
                    .app_to(Exp::Tuple(Vec::new()))
            };
            coma::Var(Ident::build(id.as_str()), ty.clone(), init, coma::IsRef::Ref)
        })
        .collect();

    // Remove the invariant from the contract here??
    let mut sig = if body_id.promoted.is_none() {
        signature_of(ctx, names, name, body_id.def_id())
    } else {
        let ret = ret.unwrap();
        Signature {
            name,
            trigger: None,
            attrs: vec![],
            retty: Some(translate_ty(ctx, names, ret.span, ret.ty)),
            args: vec![],
            contract: Contract::default(),
        }
    };
    let mut body = Expr::Defn(Box::new(Expr::Symbol("bb0".into())), true, blocks);

    let mut postcond = Expr::Symbol("return".into()).app(vec![Arg::Term(Exp::var("result"))]);

    let inferred_closure_spec = ctx.is_closure_like(body_id.def_id())
        && !ctx.sig(body_id.def_id()).contract.has_user_contract;

    // We remove the barrier around the definition in the following edge cases:
    let open_body = false
        // a closure with no contract
        || inferred_closure_spec
        // a promoted item
        || body_id.promoted.is_some()
        // a ghost closure
        || is_ghost_closure(ctx.tcx, body_id.def_id());

    let ensures = sig.contract.ensures.into_iter().map(Condition::labelled_exp);

    if !open_body {
        postcond = Expr::BlackBox(Box::new(postcond));
        postcond = ensures.rfold(postcond, |acc, cond| Expr::Assert(Box::new(cond), Box::new(acc)));

        body = Expr::BlackBox(Box::new(body))
    };

    if inferred_closure_spec {
        sig.attrs.push(Attribute::Attr("coma:extspec".into()));
    }

    body = Expr::Let(Box::new(body), vars);

    body = Expr::Defn(
        Box::new(body),
        false,
        vec![Defn {
            name: "return".into(),
            writes: Vec::new(),
            attrs: vec![],
            params: vec![Param::Term("result".into(), sig.retty.clone().unwrap())],
            body: postcond,
        }],
    );

    let requires = sig.contract.requires.into_iter().map(Condition::labelled_exp);
    if !open_body {
        body = requires.rfold(body, |acc, req| Expr::Assert(Box::new(req), Box::new(acc)));
    }
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
    coma::Defn { name: sig.name, writes: Vec::new(), attrs: sig.attrs, params, body }
}

fn component_to_defn<'tcx, N: Namer<'tcx>>(
    body: &mut Body<'tcx>,
    ctx: &Why3Generator<'tcx>,
    names: &N,
    def_id: LocalDefId,
    c: Component<BasicBlock>,
) -> coma::Defn {
    let mut lower =
        LoweringState { ctx, names, locals: &body.locals, name_supply: Default::default(), def_id };
    let (head, tl) = match c {
        Component::Vertex(v) => {
            let block = body.blocks.shift_remove(&v).unwrap();
            return block.to_why(&mut lower, v);
        }
        Component::Component(v, tls) => (v, tls),
    };

    let block = body.blocks.shift_remove(&head).unwrap();
    let mut block = block.to_why(&mut lower, head);

    let defns = tl.into_iter().map(|id| component_to_defn(body, ctx, names, def_id, id)).collect();

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
    pub(super) ctx: &'a Why3Generator<'tcx>,
    pub(super) names: &'a N,
    pub(super) locals: &'a LocalDecls<'tcx>,
    pub(super) name_supply: RefCell<NameSupply>,
    pub(super) def_id: LocalDefId,
}

impl<'a, 'tcx, N: Namer<'tcx>> LoweringState<'a, 'tcx, N> {
    pub(super) fn ty(&self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, DUMMY_SP, ty)
    }

    fn assignment(&self, lhs: &Place<'tcx>, rhs: Term, istmts: &mut Vec<IntermediateStmt>) {
        place::create_assign_inner(self, lhs, rhs, istmts)
    }

    pub(super) fn fresh_sym_from(&self, base: impl AsRef<str>) -> Symbol {
        self.name_supply.borrow_mut().freshen(Symbol::intern(base.as_ref()))
    }

    pub(super) fn fresh_from(&self, base: impl AsRef<str>) -> Ident {
        self.fresh_sym_from(base).to_string().into()
    }
}

impl<'tcx> Operand<'tcx> {
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> Exp {
        match self {
            Operand::Move(pl) | Operand::Copy(pl) => rplace_to_expr(lower, &pl, istmts),
            Operand::Constant(c) => lower_pure(lower.ctx, lower.names, &c),
            Operand::Promoted(pid, ty) => {
                let promoted = Expr::Symbol(lower.names.promoted(lower.def_id, pid));
                let var: Ident = Ident::build(&format!("pr{}", pid.as_usize()));
                istmts.push(IntermediateStmt::call(var.clone(), lower.ty(ty), promoted, vec![]));

                Exp::var(var)
            }
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
                Exp::qvar(lower.names.from_prelude(PreludeModule::Bool, "eq"))
                    .app(vec![l.to_why(lower, istmts), r.to_why(lower, istmts)])
            }
            RValue::BinOp(BinOp::Ne, l, r) if l.ty(lower.ctx.tcx, lower.locals).is_bool() => {
                Exp::qvar(lower.names.from_prelude(PreludeModule::Bool, "ne"))
                    .app(vec![l.to_why(lower, istmts), r.to_why(lower, istmts)])
            }
            RValue::BinOp(op, l, r) => {
                let l_ty = l.ty(lower.ctx.tcx, lower.locals);

                let fname = binop_to_binop(lower.names, l_ty, op);
                let call = coma::Expr::Symbol(fname);

                // some operator need to convert the right operand
                let r = match op {
                    // right operand must be converted to integer
                    BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked => {
                        let r_ty = r.ty(lower.ctx.tcx, lower.locals);

                        // rust allows shifting by a value of any integer type
                        // so we need to import the prelude for the right operand
                        let qname = match r_ty.kind() {
                            TyKind::Int(ity) => lower.names.from_prelude(ity_to_prelude(lower.ctx.tcx, *ity), "to_int"),
                            TyKind::Uint(uty) => lower.names.from_prelude(uty_to_prelude(lower.ctx.tcx, *uty), "t'int"),
                            _ => unreachable!("right operand, non-integer type for binary operation {op:?} {ty:?}"),
                        };

                        // build the expression for this convertion
                        Exp::qvar(qname).app_to(r.to_why(lower, istmts))
                    }
                    _ => r.to_why(lower, istmts),
                };

                let args = vec![Arg::Term(l.to_why(lower, istmts)), Arg::Term(r)];
                istmts.extend([IntermediateStmt::call("_ret'".into(), lower.ty(ty), call, args)]);
                // let ty = l.ty(lower.ctx.tcx, locals);
                // // Hack
                // translate_ty(ctx, names, DUMMY_SP, ty);

                Exp::var("_ret'")
                // let op_ty = l.ty(ctx.tcx, locals);
                // // Hack
                // translate_ty(ctx, names, DUMMY_SP, op_ty);
            }
            RValue::UnaryOp(UnOp::Not, arg) => {
                let a_ty = arg.ty(lower.ctx.tcx, lower.locals);
                match a_ty.kind() {
                    TyKind::Bool => arg.to_why(lower, istmts).not(),
                    TyKind::Int(_) | TyKind::Uint(_) => {
                        let prelude: PreludeModule = match a_ty.kind() {
                            TyKind::Int(ity) => ity_to_prelude(lower.ctx.tcx, *ity),
                            TyKind::Uint(uty) => uty_to_prelude(lower.ctx.tcx, *uty),
                            _ => unreachable!("this is not an executable path {ty:?}"),
                        };

                        let call = coma::Expr::Symbol(lower.names.from_prelude(prelude, "bw_not"));
                        let args = vec![Arg::Term(arg.to_why(lower, istmts))];
                        istmts.push(IntermediateStmt::call(
                            "_ret'".into(),
                            lower.ty(ty),
                            call,
                            args,
                        ));
                        Exp::var("_ret'")
                    }
                    _ => unreachable!("the not operator is not supported for {ty:?}"),
                }
            }
            RValue::UnaryOp(UnOp::Neg, arg) => {
                let prelude: PreludeModule = match ty.kind() {
                    TyKind::Int(ity) => ity_to_prelude(lower.ctx.tcx, *ity),
                    TyKind::Uint(uty) => uty_to_prelude(lower.ctx.tcx, *uty),
                    TyKind::Float(fty) => floatty_to_prelude(*fty),
                    TyKind::Bool => PreludeModule::Bool,
                    _ => unreachable!("non-primitive type for negation {ty:?}"),
                };

                let neg = lower.names.from_prelude(prelude, "neg");

                let id: Ident = "_ret".into();
                let ty = lower.ty(ty);
                let arg = arg.to_why(lower, istmts);
                istmts.push(IntermediateStmt::call(
                    id.clone(),
                    ty,
                    Expr::Symbol(neg),
                    vec![Arg::Term(arg)],
                ));

                Exp::var(id)
            }
            RValue::Constructor(id, subst, args) => {
                if lower.ctx.def_kind(id) == DefKind::Closure {
                    lower.names.dependency(Dependency::Item(id, subst));
                }
                let args = args.into_iter().map(|a| a.to_why(lower, istmts)).collect();
                constructor(lower.names, args, id, subst)
            }
            RValue::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(lower, istmts)).collect())
            }
            RValue::Cast(e, source, target) => {
                match source.kind() {
                    TyKind::Bool => {
                        let of_fname = match target.kind() {
                            TyKind::Int(ity) => lower
                                .names
                                .from_prelude(ity_to_prelude(lower.ctx.tcx, *ity), "of_bool"),
                            TyKind::Uint(uty) => lower
                                .names
                                .from_prelude(uty_to_prelude(lower.ctx.tcx, *uty), "of_bool"),
                            _ => lower.ctx.crash_and_error(
                                DUMMY_SP,
                                "bool cast to non integral casts are currently unsupported",
                            ),
                        };
                        let of_ret_id: Ident = "_ret_from".into();
                        let of_arg = Arg::Term(e.to_why(lower, istmts));
                        istmts.extend([IntermediateStmt::call(
                            of_ret_id.clone(),
                            lower.ty(ty),
                            Expr::Symbol(of_fname),
                            vec![of_arg],
                        )]);
                        Exp::var(of_ret_id)
                    }
                    _ => {
                        let tmp_ty = Type::TConstructor(
                            if lower.names.bitwise_mode() { "BV256.t" } else { "int" }.into(),
                        );

                        let to_fname = match source.kind() {
                            TyKind::Int(ity) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "to_BV256" } else { "to_int" };
                                lower
                                    .names
                                    .from_prelude(ity_to_prelude(lower.ctx.tcx, *ity), fct_name)
                            }
                            TyKind::Uint(ity) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "to_BV256" } else { "to_int" };
                                lower
                                    .names
                                    .from_prelude(uty_to_prelude(lower.ctx.tcx, *ity), fct_name)
                            }
                            _ => lower.ctx.crash_and_error(
                                DUMMY_SP,
                                &format!("casts {:?} are currently unsupported", source.kind()),
                            ),
                        };

                        // convert source to BV256.t / int
                        let to_ret_id: Ident = "_ret_to".into();
                        let to_arg = Arg::Term(e.to_why(lower, istmts));
                        istmts.push(IntermediateStmt::call(
                            to_ret_id.clone(),
                            tmp_ty,
                            Expr::Symbol(to_fname),
                            vec![to_arg],
                        ));

                        // convert BV256.t / int to target
                        let of_ret_id: Ident = "_ret_from".into();
                        let of_fname = match target.kind() {
                            TyKind::Int(ity) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                                lower
                                    .names
                                    .from_prelude(ity_to_prelude(lower.ctx.tcx, *ity), fct_name)
                            }
                            TyKind::Uint(uty) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                                lower
                                    .names
                                    .from_prelude(uty_to_prelude(lower.ctx.tcx, *uty), fct_name)
                            }
                            TyKind::Char => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                                lower.names.from_prelude(PreludeModule::Char, fct_name)
                            }
                            _ => lower.ctx.crash_and_error(
                                DUMMY_SP,
                                "Non integral casts are currently unsupported",
                            ),
                        };

                        // create final statement
                        istmts.extend([IntermediateStmt::call(
                            of_ret_id.clone(),
                            lower.ty(ty),
                            Expr::Symbol(of_fname),
                            vec![Arg::Term(Term::Var(to_ret_id))],
                        )]);
                        Exp::var(of_ret_id)
                    }
                }
            }
            RValue::Len(op) => Exp::qvar(lower.names.from_prelude(PreludeModule::Slice, "length"))
                .app_to(op.to_why(lower, istmts)),
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
                        Exp::qvar("Seq.get".into())
                            .app(vec![
                                arr_elts.clone(),
                                Exp::Const(Constant::Int(ix as i128, None)),
                            ])
                            .eq(f.to_why(lower, istmts))
                    })
                    .chain([Exp::qvar("Seq.length".into())
                        .app_to(arr_elts.clone())
                        .eq(Exp::Const(Constant::Int(len as i128, None)))])
                    .reduce(Exp::log_and)
                    .expect("array literal missing assumption");
                assumptions.reassociate();

                istmts.push(IntermediateStmt::Assume(assumptions));
                Exp::var(id)
            }
            RValue::Repeat(e, len) => {
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
                    Expr::Symbol(lower.names.from_prelude(PreludeModule::Slice, "create")),
                    args,
                ));

                Exp::var("_res")
            }
            RValue::Snapshot(t) => lower_pure(lower.ctx, lower.names, &t),
            RValue::Borrow(_, _, _) => unreachable!(), // Handled in Statement::to_why
            RValue::UnaryOp(UnOp::PtrMetadata, op) => {
                match op.ty(lower.ctx.tcx, lower.locals).kind() {
                    TyKind::Ref(_, ty, mu) => {
                        assert!(ty.is_slice());
                        let mut op = op.to_why(lower, istmts);
                        if mu.is_mut() {
                            op = op.field("current")
                        }
                        Exp::qvar(lower.names.from_prelude(PreludeModule::Slice, "length"))
                            .app_to(op)
                    }
                    TyKind::RawPtr(ty, _) => {
                        assert!(ty.is_slice());
                        Exp::qvar(lower.names.from_prelude(PreludeModule::Slice, "slice_ptr_len"))
                            .app_to(op.to_why(lower, istmts))
                    }
                    _ => unreachable!(),
                }
            }
            RValue::Ptr(pl) => {
                istmts.push(IntermediateStmt::call(
                    "_ptr".into(),
                    lower.ty(ty),
                    Expr::Symbol("Opaque.fresh_ptr".into()),
                    vec![],
                ));

                if pl.ty(lower.ctx.tcx, lower.locals).is_slice() {
                    let lhs =
                        Exp::qvar(lower.names.from_prelude(PreludeModule::Slice, "slice_ptr_len"))
                            .app_to(Exp::qvar("_ptr".into()));
                    let rhs = Exp::qvar(lower.names.from_prelude(PreludeModule::Slice, "length"))
                        .app_to(rplace_to_expr(lower, &pl, istmts));
                    istmts.push(IntermediateStmt::Assume(lhs.eq(rhs)));
                }

                Exp::var("_ptr")
            }
        };

        e
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
                let ty = switch.ty(lower.ctx.tcx, lower.locals);
                let discr = switch.to_why(lower, &mut istmts);
                (istmts, branches.to_why(lower.ctx, lower.names, discr, &ty))
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
        ctx: &Why3Generator<'tcx>,
        names: &N,
        discr: Exp,
        discr_ty: &Ty<'tcx>,
    ) -> coma::Expr {
        match self {
            Branches::Int(brs, def) => {
                let TyKind::Int(ity) = discr_ty.kind() else {
                    panic!("Branches::Int try to evaluate a type that is not Int")
                };

                let mut brs = mk_switch_branches(
                    discr,
                    brs.into_iter()
                        .map(|(mut val, tgt)| {
                            let why_ty = Type::TConstructor(
                                names.from_prelude(ity_to_prelude(ctx.tcx, *ity), "t"),
                            );
                            let e = if names.bitwise_mode() {
                                // In bitwise mode, integers are bit vectors, whose literals are always unsigned
                                if val < 0 && *ity != IntTy::I128 {
                                    let target_width = ctx.tcx.sess.target.pointer_width;
                                    val += 1 << ity.normalize(target_width).bit_width().unwrap();
                                }
                                Exp::Const(Constant::Uint(val as u128, Some(why_ty)))
                            } else {
                                Exp::Const(Constant::Int(val, Some(why_ty)))
                            };
                            (e, mk_goto(tgt))
                        })
                        .collect(),
                );

                brs.push(Defn::simple("default", Expr::BlackBox(Box::new(mk_goto(def)))));
                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
            Branches::Uint(brs, def) => {
                let uty = match discr_ty.kind() {
                    TyKind::Uint(uty) => uty,
                    _ => panic!("Branches::Uint try to evaluate a type that is not Uint"),
                };

                let mut brs = mk_switch_branches(
                    discr,
                    brs.into_iter()
                        .map(|(val, tgt)| {
                            let why_ty = Type::TConstructor(
                                names.from_prelude(uty_to_prelude(ctx.tcx, *uty), "t"),
                            );
                            let e = Exp::Const(Constant::Uint(val, Some(why_ty)));
                            (e, mk_goto(tgt))
                        })
                        .collect(),
                );

                brs.push(Defn::simple("default", Expr::BlackBox(Box::new(mk_goto(def)))));
                Expr::Defn(Box::new(Expr::Any), false, brs)
            }
            Branches::Constructor(adt, substs, vars, def) => {
                let brs = mk_adt_switch(ctx, names, adt, substs, discr, vars, def);
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
    ctx: &Why3Generator<'tcx>,
    names: &N,
    adt: AdtDef<'tcx>,
    subst: GenericArgsRef<'tcx>,
    discr: Exp,
    brch: Vec<(VariantIdx, BasicBlock)>,
    default: Option<BasicBlock>,
) -> Vec<coma::Defn> {
    assert!(adt.is_enum());

    let mut brch = brch.into_iter().peekable();

    let res = adt
        .variants()
        .iter_enumerated()
        .map(|(ix, var)| {
            let tgt = if brch.peek().is_some_and(|&(vix, _)| vix == ix) {
                brch.next().unwrap().1
            } else {
                default.unwrap()
            };

            let (params, ids) = var
                .fields
                .iter_enumerated()
                .map(|(ix, field)| {
                    let id: Ident = format!("x{}", ix.as_usize()).into();
                    (
                        Param::Term(
                            id.clone(),
                            translate_ty(ctx, names, DUMMY_SP, field.ty(ctx.tcx, subst)),
                        ),
                        Exp::var(id),
                    )
                })
                .unzip();

            let cons = names.constructor(var.def_id, subst);

            let body = Exp::qvar(cons).app(ids);
            let body = coma::Expr::Assert(
                Box::new(discr.clone().eq(body)),
                Box::new(coma::Expr::BlackBox(Box::new(mk_goto(tgt)))),
            );
            let name = format!("br{}", ix.as_usize()).into();

            coma::Defn { name, body, params, writes: Vec::new(), attrs: vec![] }
        })
        .collect();
    assert!(brch.next().is_none());
    res
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

        for i in self.invariants.into_iter().rev() {
            body = Expr::Assert(
                Box::new(Term::Attr(
                    Attribute::Attr(i.expl),
                    Box::new(lower_pure(lower.ctx, lower.names, &i.body)),
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
                attrs: vec![],
                params: vec![Param::Term(id, ty)],
                body: Expr::BlackBox(Box::new(tail)),
            }],
        ),
    })
}

pub(crate) fn borrow_generated_id<'tcx, V: Debug, T: Debug, N: Namer<'tcx>>(
    names: &N,
    original_borrow: Exp,
    projection: &[ProjectionElem<V, T>],
    mut translate_index: impl FnMut(&V) -> Exp,
) -> Exp {
    let mut borrow_id = Exp::Call(
        Box::new(Exp::qvar(names.from_prelude(PreludeModule::Borrow, "get_id"))),
        vec![original_borrow],
    );
    for proj in projection {
        match proj {
            ProjectionElem::Deref => {
                // TODO: If this is a deref of a mutable borrow, the id should change !
            }
            ProjectionElem::Field(idx, _) => {
                borrow_id = Exp::Call(
                    Box::new(Exp::qvar(names.from_prelude(PreludeModule::Borrow, "inherit_id"))),
                    vec![borrow_id, Exp::Const(Constant::Int(idx.as_u32() as i128 + 1, None))],
                );
            }
            ProjectionElem::Index(x) => {
                borrow_id = Exp::Call(
                    Box::new(Exp::qvar(names.from_prelude(PreludeModule::Borrow, "inherit_id"))),
                    vec![borrow_id, translate_index(x)],
                );
            }

            ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {
                // those should inherit a different id instead
                todo!("Unsupported projection {proj:?} in reborrow")
            }
            // Nothing to do
            ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::Subtype(_) => {}
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
    fn call(id: Ident, ty: Type, f: coma::Expr, args: Vec<coma::Arg>) -> Self {
        IntermediateStmt::Call(vec![Param::Term(id, ty)], f, args)
    }
}

impl<'tcx> Statement<'tcx> {
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
    ) -> Vec<IntermediateStmt> {
        let mut istmts = Vec::new();
        match self {
            Statement::Assignment(lhs, RValue::Borrow(bor_kind, rhs, triv_inv), _span) => {
                let lhs_ty = lhs.ty(lower.ctx.tcx, lower.locals);
                let lhs_ty_low = lower.ty(lhs_ty);
                let rhs_ty = rhs.ty(lower.ctx.tcx, lower.locals);
                let rhs_ty_low = lower.ty(rhs_ty);
                let rhs_local_ty = PlaceTy::from_ty(lower.locals[&rhs.local].ty);

                let rhs_inv_fun = if matches!(triv_inv, TrivialInv::NonTrivial) {
                    Some(Exp::qvar(lower.names.ty_inv(rhs_ty)))
                } else {
                    None
                };

                let func = coma::Expr::Symbol(lower.names.from_prelude(
                    PreludeModule::Borrow,
                    match bor_kind {
                        BorrowKind::Mut => "borrow_mut",
                        BorrowKind::Final(_) => "borrow_final",
                    },
                ));

                let bor_id_arg;
                let rhs_rplace;
                let rhs_constr;

                if let BorrowKind::Final(deref_index) = bor_kind {
                    let (original_borrow_ty, original_borrow, original_borrow_constr) =
                        place::projections_to_expr(
                            lower,
                            &mut istmts,
                            rhs_local_ty,
                            place::Focus::new(|_| Exp::var(ident_of(rhs.local))),
                            Box::new(|_, x| x),
                            &rhs.projection[..deref_index],
                        );
                    let (_, foc, constr) = place::projections_to_expr(
                        lower,
                        &mut istmts,
                        original_borrow_ty,
                        original_borrow.clone(),
                        original_borrow_constr,
                        &rhs.projection[deref_index..],
                    );
                    rhs_rplace = foc.call(&mut istmts);
                    rhs_constr = constr;

                    let borrow_id = borrow_generated_id(
                        lower.names,
                        original_borrow.call(&mut istmts),
                        &rhs.projection[deref_index + 1..],
                        |sym| {
                            let v = ident_of(*sym);
                            let qname = lower.names.from_prelude(
                                uty_to_prelude(lower.ctx.tcx, UintTy::Usize),
                                "t'int",
                            );

                            Exp::Call(Box::new(Exp::qvar(qname)), vec![Exp::var(v)])
                        },
                    );

                    bor_id_arg = Some(Arg::Term(borrow_id));
                } else {
                    let (_, foc, constr) = place::projections_to_expr(
                        &lower,
                        &mut istmts,
                        rhs_local_ty,
                        place::Focus::new(|_| Exp::var(ident_of(rhs.local))),
                        Box::new(|_, x| x),
                        &rhs.projection,
                    );
                    rhs_rplace = foc.call(&mut istmts);
                    rhs_constr = constr;
                    bor_id_arg = None;
                }

                if let Some(ref rhs_inv_fun) = rhs_inv_fun {
                    istmts.push(IntermediateStmt::Assert(
                        rhs_inv_fun.clone().app_to(rhs_rplace.clone()),
                    ));
                }

                let mut args = vec![Arg::Ty(rhs_ty_low), Arg::Term(rhs_rplace)];
                args.extend(bor_id_arg);

                let borrow_call = IntermediateStmt::call("_ret'".into(), lhs_ty_low, func, args);
                istmts.push(borrow_call);
                lower.assignment(&lhs, Exp::var("_ret'"), &mut istmts);

                let reassign = Exp::var("_ret'").field("final");

                if let Some(rhs_inv_fun) = rhs_inv_fun {
                    istmts.push(IntermediateStmt::Assume(rhs_inv_fun.app_to(reassign.clone())));
                }

                let new_rhs = rhs_constr(&mut istmts, reassign);
                istmts.push(IntermediateStmt::Assign(Ident::build(rhs.local.as_str()), new_rhs));
            }
            Statement::Assignment(lhs, e, _span) => {
                let rhs = e.to_why(lower, lhs.ty(lower.ctx.tcx, lower.locals), &mut istmts);
                lower.assignment(&lhs, rhs, &mut istmts);
            }
            Statement::Call(dest, fun_id, subst, args, _) => {
                let (fun_exp, args) = func_call_to_why3(lower, fun_id, subst, args, &mut istmts);
                let ty = dest.ty(lower.ctx.tcx, lower.locals);
                let ty = lower.ty(ty);

                istmts.push(IntermediateStmt::call("_ret'".into(), ty, fun_exp, args));
                lower.assignment(&dest, Exp::var("_ret'"), &mut istmts);
            }
            Statement::Resolve { did, subst, pl } => {
                let rp = Exp::qvar(lower.names.item(did, subst));
                let loc = pl.local;

                let bound = lower.fresh_sym_from("x");

                let pat = pattern_of_place(lower.ctx.tcx, lower.locals, pl, bound);

                let pat = lower_pat(lower.ctx, lower.names, &pat);
                let exp = if let Pattern::VarP(_) = pat {
                    rp.app_to(Exp::var(ident_of(loc)))
                } else {
                    Exp::Match(
                        Box::new(Exp::var(ident_of(loc))),
                        vec![
                            (pat, rp.app_to(Exp::var(bound.as_str()))),
                            (Pattern::Wildcard, Exp::mk_true()),
                        ],
                    )
                };

                istmts.extend([IntermediateStmt::Assume(exp)]);
            }
            Statement::Assertion { cond, msg, trusted } => {
                let e = Exp::Attr(
                    Attribute::Attr(msg),
                    Box::new(lower_pure(lower.ctx, lower.names, &cond)),
                );
                if trusted {
                    istmts.push(IntermediateStmt::Assume(e))
                } else {
                    istmts.push(IntermediateStmt::Assert(e))
                }
            }
            Statement::AssertTyInv { pl } => {
                let inv_fun = Exp::qvar(lower.names.ty_inv(pl.ty(lower.ctx.tcx, lower.locals)));
                let loc = pl.local;

                let bound = lower.fresh_sym_from("x");

                let pat = pattern_of_place(lower.ctx.tcx, lower.locals, pl, bound);
                let pat = lower_pat(lower.ctx, lower.names, &pat);
                let exp = if let Pattern::VarP(_) = pat {
                    inv_fun.app_to(Exp::var(ident_of(loc)))
                } else {
                    Exp::Match(
                        Box::new(Exp::var(ident_of(loc))),
                        vec![
                            (pat, inv_fun.app_to(Exp::var(bound.as_str()))),
                            (Pattern::Wildcard, Exp::mk_true()),
                        ],
                    )
                };

                let exp = Exp::Attr(Attribute::Attr(format!("expl:type invariant")), Box::new(exp));

                istmts.push(IntermediateStmt::Assert(exp));
            }
        }
        istmts
    }
}

/// Transform a place into a deeply nested pattern match, binding the pointed item into `binder`
/// TODO: Transform this into a `match_place_logic` construct that handles everything
fn pattern_of_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    locals: &fmir::LocalDecls<'tcx>,
    pl: fmir::Place<'tcx>,
    binder: Symbol,
) -> pearlite::Pattern<'tcx> {
    let mut pat = pearlite::Pattern::Binder(binder);

    for (pl, el) in pl.iter_projections().rev() {
        let ty = pl.ty(tcx, locals);
        match el {
            ProjectionElem::Deref => match ty.ty.kind() {
                TyKind::Ref(_, _, mutbl) => match mutbl {
                    Mutability::Not => {
                        pat = pearlite::Pattern::Deref {
                            pointee: Box::new(pat),
                            kind: PointerKind::Shr,
                        }
                    }
                    Mutability::Mut => {
                        pat = pearlite::Pattern::Deref {
                            pointee: Box::new(pat),
                            kind: PointerKind::Mut,
                        }
                    }
                },
                _ if ty.ty.is_box() => {
                    pat =
                        pearlite::Pattern::Deref { pointee: Box::new(pat), kind: PointerKind::Box }
                }
                _ => {
                    unreachable!("unsupported type of deref pattern: {:?}", ty.ty);
                }
            },
            ProjectionElem::Field(fidx, _) => match ty.ty.kind() {
                TyKind::Adt(adt, substs) => {
                    let variant_def = &adt.variants()[ty.variant_index.unwrap_or(VariantIdx::ZERO)];
                    let fields_len = variant_def.fields.len();
                    let variant = variant_def.def_id;
                    let mut fields = vec![pearlite::Pattern::Wildcard; fields_len];
                    fields[fidx.as_usize()] = pat;
                    pat = pearlite::Pattern::Constructor { variant, substs, fields }
                }
                TyKind::Tuple(tys) => {
                    let mut fields = vec![pearlite::Pattern::Wildcard; tys.len()];
                    fields[fidx.as_usize()] = pat;
                    pat = pearlite::Pattern::Tuple(fields)
                }
                TyKind::Closure(did, substs) => {
                    let mut fields: Vec<_> = substs
                        .as_closure()
                        .upvar_tys()
                        .iter()
                        .map(|_| pearlite::Pattern::Wildcard)
                        .collect();
                    fields[fidx.as_usize()] = pat;
                    pat = pearlite::Pattern::Constructor { variant: *did, substs, fields }
                }
                _ => unreachable!(),
            },
            ProjectionElem::Downcast(_, _) => {}

            ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {
                todo!("Array and slice patterns are currently not supported")
            }

            ProjectionElem::Index(_)
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::Subtype(_) => {
                unreachable!("These ProjectionElem should not be move paths")
            }
        }
    }

    pat
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

    let fname = lower.names.item(id, subst);

    (coma::Expr::Symbol(fname), args)
}

pub(crate) fn binop_to_binop<'tcx, N: Namer<'tcx>>(names: &N, ty: Ty, op: mir::BinOp) -> QName {
    let prelude: PreludeModule = match ty.kind() {
        TyKind::Int(ity) => ity_to_prelude(names.tcx(), *ity),
        TyKind::Uint(uty) => uty_to_prelude(names.tcx(), *uty),
        TyKind::Float(fty) => floatty_to_prelude(*fty),
        TyKind::Bool => PreludeModule::Bool,
        TyKind::Char => PreludeModule::Char,
        _ => unreachable!("non-primitive type for binary operation {op:?} {ty:?}"),
    };

    use BinOp::*;
    let name = match op {
        Add => "add",
        AddUnchecked => "add",
        Sub => "sub",
        SubUnchecked => "sub",
        Mul => "mul",
        MulUnchecked => "mul",
        Div => "div",
        Rem => "rem",
        BitXor => "bw_xor",
        BitAnd => "bw_and",
        BitOr => "bw_or",
        Shl => "shl",
        ShlUnchecked => "shl",
        Shr => "shr",
        ShrUnchecked => "shr",
        Eq => "eq",
        Lt => "lt",
        Le => "le",
        Ne => "ne",
        Ge => "ge",
        Gt => "gt",
        Cmp | AddWithOverflow | SubWithOverflow | MulWithOverflow => todo!(),
        Offset => unimplemented!("pointer offsets are unsupported"),
    };

    names.from_prelude(prelude, name)
}
