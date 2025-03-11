use crate::{
    backend::{
        NameSupply, Namer, Why3Generator,
        clone_map::PreMod,
        dependency::Dependency,
        is_trusted_item,
        optimization::{gather_usage, infer_proph_invariants, simplify_fmir},
        place::{Focus, create_assign_inner, projections_to_expr, rplace_to_expr},
        signature::sig_to_why3,
        term::{lower_pat, lower_pure},
        ty::{
            constructor, floatty_to_prelude, int_ty, ity_to_prelude, translate_ty, uty_to_prelude,
        },
        wto::{Component, weak_topological_order},
    },
    ctx::{BodyId, Dependencies},
    fmir::{Body, BorrowKind, Operand, TrivialInv},
    naming::ident_of,
    pearlite::{Pattern, PointerKind},
    translated_item::FileModule,
    translation::fmir::{Block, Branches, LocalDecls, Place, RValue, Statement, Terminator},
};

use petgraph::graphmap::DiGraphMap;
use rustc_ast::Mutability;
use rustc_hir::{
    Safety,
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{BasicBlock, BinOp, ProjectionElem, START_BLOCK, UnOp, tcx::PlaceTy},
    ty::{AdtDef, GenericArgsRef, Ty, TyCtxt, TyKind},
};
use rustc_span::{DUMMY_SP, Symbol};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{IntTy, UintTy};
use std::{
    cell::RefCell,
    fmt::Debug,
    iter::{once, repeat_n},
};
use why3::{
    Ident, QName,
    coma::{Arg, Defn, Expr, IsRef, Param, Term, Var},
    declaration::{
        Attribute, Condition, Contract, Decl, Meta, MetaArg, MetaIdent, Module, Signature,
    },
    exp::{Binder, Constant, Exp, Pattern as WPattern},
    ty::Type,
};

pub(crate) fn translate_function<'tcx, 'sess>(
    ctx: &Why3Generator<'tcx>,
    def_id: DefId,
) -> Option<FileModule> {
    let mut names = Dependencies::new(ctx, def_id);

    if !def_id.is_local() || !ctx.has_body(def_id) || is_trusted_item(ctx.tcx, def_id) {
        return None;
    }

    let name = names.item(names.self_id, names.self_subst).as_ident();
    let body = Decl::Coma(to_why(ctx, &mut names, name, BodyId::new(def_id.expect_local(), None)));

    let mut decls = names.provide_deps(ctx);
    decls.push(Decl::Meta(Meta {
        name: MetaIdent::String("compute_max_steps".into()),
        args: Box::new([MetaArg::Integer(1_000_000)]),
    }));
    decls.push(body);

    let attrs = ctx.span_attr(ctx.def_span(def_id)).into_iter().collect();
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Some(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } })
}

pub fn val<'tcx>(_: &Why3Generator<'tcx>, sig: Signature) -> Decl {
    let params = sig
        .args
        .into_iter()
        .flat_map(|b| b.var_type_pairs())
        .map(|(v, ty)| Param::Term(v, ty))
        .chain([Param::Cont(
            "return".into(),
            Box::new([]),
            Box::new([Param::Term("ret".into(), sig.retty.clone().unwrap())]),
        )])
        .collect();

    let requires = sig.contract.requires.into_iter().map(Condition::labelled_exp);
    let body = requires.rfold(Expr::Any, |acc, cond| Expr::assert(cond, acc));

    let mut postcond = Expr::Symbol("return".into()).app([Arg::Term(Exp::var("result"))]);
    postcond = postcond.black_box();
    let ensures = sig.contract.ensures.into_iter().map(Condition::unlabelled_exp);
    postcond = ensures.rfold(postcond, |acc, cond| Expr::assert(cond, acc));

    let body = Expr::Defn(
        body.boxed(),
        false,
        Box::new([Defn {
            name: "return".into(),
            attrs: vec![],
            params: Box::new([Param::Term("result".into(), sig.retty.clone().unwrap())]),
            body: postcond,
        }]),
    );
    Decl::Coma(Defn { name: sig.name, attrs: vec![], params, body })
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
) -> Defn {
    let mut body = ctx.fmir_body(body_id).clone();

    simplify_fmir(gather_usage(&body), &mut body);

    let wto = weak_topological_order(&node_graph(&body), START_BLOCK);
    infer_proph_invariants(ctx, &mut body);

    let blocks: Box<[Defn]> = wto
        .into_iter()
        .map(|c| component_to_defn(&mut body, ctx, names, body_id.def_id, c))
        .collect();
    let ret = body.locals.first().map(|(_, decl)| decl.clone());

    let vars: Box<[_]> = body
        .locals
        .into_iter()
        .map(|(id, decl)| {
            let ty = translate_ty(ctx, names, decl.span, decl.ty);

            let init = if decl.arg {
                Exp::var(Ident::build(id.as_str()))
            } else {
                Exp::qvar(names.in_pre(PreMod::Any, "any_l")).app([Exp::unit()])
            };
            Var(Ident::build(id.as_str()), ty.clone(), init, IsRef::Ref)
        })
        .collect();

    // Remove the invariant from the contract here??
    let mut sig = if body_id.promoted.is_none() {
        let def_id = body_id.def_id();
        let pre_sig = ctx.sig(def_id).clone().normalize(ctx.tcx, ctx.typing_env(def_id));
        sig_to_why3(ctx, names, name, pre_sig, def_id)
    } else {
        let ret = ret.unwrap();
        Signature {
            name,
            trigger: None,
            attrs: vec![],
            retty: Some(translate_ty(ctx, names, ret.span, ret.ty)),
            args: Box::new([]),
            contract: Contract::default(),
        }
    };
    let mut body = Expr::Defn(Expr::Symbol("bb0".into()).boxed(), true, blocks);

    let mut postcond = Expr::Symbol("return".into()).app([Arg::Term(Exp::var("result"))]);

    let inferred_closure_spec = ctx.is_closure_like(body_id.def_id())
        && !ctx.sig(body_id.def_id()).contract.has_user_contract;

    // We remove the barrier around the definition in the following edge cases:
    let open_body = false
        // a closure with no contract
        || inferred_closure_spec
        // a promoted item
        || body_id.promoted.is_some();

    let ensures = sig.contract.ensures.into_iter().map(Condition::labelled_exp);

    if !open_body {
        postcond = postcond.black_box();
        postcond = ensures.rfold(postcond, |acc, cond| Expr::assert(cond, acc));

        body = body.black_box()
    };

    if inferred_closure_spec {
        sig.attrs.push(Attribute::Attr("coma:extspec".into()));
    }

    body = body.let_(vars);

    body = Expr::Defn(
        body.boxed(),
        false,
        Box::new([Defn {
            name: "return".into(),
            attrs: vec![],
            params: Box::new([Param::Term("result".into(), sig.retty.clone().unwrap())]),
            body: postcond,
        }]),
    );

    let requires = sig.contract.requires.into_iter().map(Condition::labelled_exp);
    if !open_body {
        body = requires.rfold(body, |acc, req| Expr::assert(req, acc));
    }
    let params = sig
        .args
        .into_iter()
        .flat_map(|b| b.var_type_pairs())
        .map(|(v, ty)| Param::Term(v, ty))
        .chain([Param::Cont(
            "return".into(),
            Box::new([]),
            Box::new([Param::Term("ret".into(), sig.retty.unwrap())]),
        )])
        .collect();
    Defn { name: sig.name, attrs: sig.attrs, params, body }
}

fn component_to_defn<'tcx, N: Namer<'tcx>>(
    body: &mut Body<'tcx>,
    ctx: &Why3Generator<'tcx>,
    names: &N,
    def_id: LocalDefId,
    c: Component<BasicBlock>,
) -> Defn {
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
        block.body = block.body.black_box();
    }

    let inner = Expr::Defn(block.body.boxed(), true, defns);
    block.body = Expr::Defn(
        Expr::Symbol(block.name.clone().into()).boxed(),
        true,
        Box::new([Defn::simple(block.name.clone(), inner)]),
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
        create_assign_inner(self, lhs, rhs, istmts)
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
                let var = Ident::build(&format!("pr{}", pid.as_usize()));
                istmts.push(IntermediateStmt::call(
                    var.clone(),
                    lower.ty(ty),
                    lower.names.promoted(lower.def_id, pid),
                    [],
                ));

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
        match self {
            RValue::Operand(op) => op.to_why(lower, istmts),
            RValue::BinOp(op, l, r) => {
                let l_ty = l.ty(lower.ctx.tcx, lower.locals);

                match (op, l_ty.kind()) {
                    (_, TyKind::Float(_)) => (),
                    (BinOp::Eq, _) => return l.to_why(lower, istmts).eq(r.to_why(lower, istmts)),
                    (BinOp::Ne, _) => return l.to_why(lower, istmts).neq(r.to_why(lower, istmts)),
                    _ => (),
                }

                let prelude = match l_ty.kind() {
                    TyKind::Int(ity) => ity_to_prelude(lower.ctx.tcx, *ity),
                    TyKind::Uint(uty) => uty_to_prelude(lower.ctx.tcx, *uty),
                    TyKind::Float(fty) => floatty_to_prelude(*fty),
                    TyKind::Bool => PreMod::Bool,
                    TyKind::Char => PreMod::Char,
                    _ => unreachable!("non-primitive type for binary operation {op:?} {ty:?}"),
                };

                // shifts need to convert the right operand
                let r = match op {
                    // right operand must be converted to integer
                    BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked => {
                        let r_ty = r.ty(lower.ctx.tcx, lower.locals);

                        // rust allows shifting by a value of any integer type
                        // so we need to import the prelude for the right operand
                        let qname = match r_ty.kind() {
                            TyKind::Int(ity) => {
                                lower.names.in_pre(ity_to_prelude(lower.ctx.tcx, *ity), "to_int")
                            }
                            TyKind::Uint(uty) => {
                                lower.names.in_pre(uty_to_prelude(lower.ctx.tcx, *uty), "t'int")
                            }
                            _ => unreachable!(
                                "right operand, non-integer type for binary operation {op:?} {ty:?}"
                            ),
                        };

                        // build the expression for this convertion
                        Exp::qvar(qname).app([r.to_why(lower, istmts)])
                    }
                    _ => r.to_why(lower, istmts),
                };

                use BinOp::*;
                let (opname, logic) = match op {
                    Add | AddUnchecked => ("add", false),
                    Sub | SubUnchecked => ("sub", false),
                    Mul | MulUnchecked => ("mul", false),
                    Div => ("div", false),
                    Rem => ("rem", false),
                    Shl | ShlUnchecked => ("shl", false),
                    Shr | ShrUnchecked => ("shr", false),

                    Eq => ("eq", true),
                    Ne => ("ne", true),
                    Lt => ("lt", true),
                    Le => ("le", true),
                    Ge => ("ge", true),
                    Gt => ("gt", true),
                    BitXor => ("bw_xor", true),
                    BitAnd => ("bw_and", true),
                    BitOr => ("bw_or", true),

                    Cmp | AddWithOverflow | SubWithOverflow | MulWithOverflow => todo!(),
                    Offset => unimplemented!("pointer offsets are unsupported"),
                };

                let fname = lower.names.in_pre(prelude, opname);
                let args = [l.to_why(lower, istmts), r];

                if logic {
                    Exp::qvar(fname).app(args)
                } else {
                    istmts.push(IntermediateStmt::call(
                        "_ret'".into(),
                        lower.ty(ty),
                        fname,
                        args.map(Arg::Term),
                    ));
                    Exp::var("_ret'")
                }
            }
            RValue::UnaryOp(UnOp::Not, arg) => {
                let a_ty = arg.ty(lower.ctx.tcx, lower.locals);
                match a_ty.kind() {
                    TyKind::Bool => arg.to_why(lower, istmts).not(),
                    TyKind::Int(_) | TyKind::Uint(_) => {
                        let prelude: PreMod = match a_ty.kind() {
                            TyKind::Int(ity) => ity_to_prelude(lower.ctx.tcx, *ity),
                            TyKind::Uint(uty) => uty_to_prelude(lower.ctx.tcx, *uty),
                            _ => unreachable!("this is not an executable path {ty:?}"),
                        };

                        Exp::qvar(lower.names.in_pre(prelude, "bw_not"))
                            .app(vec![arg.to_why(lower, istmts)])
                    }
                    _ => unreachable!("the not operator is not supported for {ty:?}"),
                }
            }
            RValue::UnaryOp(UnOp::Neg, arg) => {
                let prelude: PreMod = match ty.kind() {
                    TyKind::Int(ity) => ity_to_prelude(lower.ctx.tcx, *ity),
                    TyKind::Float(fty) => floatty_to_prelude(*fty),
                    _ => unreachable!("non-primitive type for negation {ty:?}"),
                };

                let neg = lower.names.in_pre(prelude, "neg");
                let id: Ident = "_ret".into();
                let arg = Arg::Term(arg.to_why(lower, istmts));
                istmts.push(IntermediateStmt::call(id.clone(), lower.ty(ty), neg, [arg]));

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
                        let prelude = match target.kind() {
                            TyKind::Int(ity) => ity_to_prelude(lower.ctx.tcx, *ity),
                            TyKind::Uint(uty) => uty_to_prelude(lower.ctx.tcx, *uty),
                            _ => lower.ctx.crash_and_error(
                                DUMMY_SP,
                                "bool cast to non integral casts are currently unsupported",
                            ),
                        };
                        let arg = e.to_why(lower, istmts);
                        Exp::qvar(lower.names.in_pre(prelude, "of_bool")).app(vec![arg])
                    }
                    _ => {
                        // convert source to BV256.t / int
                        let to_fname = match source.kind() {
                            TyKind::Int(ity) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "to_BV256" } else { "to_int" };
                                lower.names.in_pre(ity_to_prelude(lower.ctx.tcx, *ity), fct_name)
                            }
                            TyKind::Uint(ity) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "to_BV256" } else { "t'int" };
                                lower.names.in_pre(uty_to_prelude(lower.ctx.tcx, *ity), fct_name)
                            }
                            _ => lower.ctx.crash_and_error(
                                DUMMY_SP,
                                &format!("casts {:?} are currently unsupported", source.kind()),
                            ),
                        };
                        let to_exp = Exp::qvar(to_fname).app(vec![e.to_why(lower, istmts)]);

                        // convert BV256.t / int to target
                        let of_fname = match target.kind() {
                            TyKind::Int(ity) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                                lower.names.in_pre(ity_to_prelude(lower.ctx.tcx, *ity), fct_name)
                            }
                            TyKind::Uint(uty) => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                                lower.names.in_pre(uty_to_prelude(lower.ctx.tcx, *uty), fct_name)
                            }
                            TyKind::Char => {
                                let fct_name =
                                    if lower.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                                lower.names.in_pre(PreMod::Char, fct_name)
                            }
                            _ => lower.ctx.crash_and_error(
                                DUMMY_SP,
                                "Non integral casts are currently unsupported",
                            ),
                        };

                        // create final statement
                        let of_ret_id: Ident = "_ret_from".into();
                        istmts.push(IntermediateStmt::call(
                            of_ret_id.clone(),
                            lower.ty(ty),
                            of_fname,
                            [Arg::Term(to_exp)],
                        ));
                        Exp::var(of_ret_id)
                    }
                }
            }
            RValue::Len(op) => Exp::qvar(lower.names.in_pre(PreMod::Slice, "length"))
                .app([op.to_why(lower, istmts)]),
            RValue::Array(fields) => {
                let id = Ident::build("__arr_temp");
                let ty = lower.ty(ty);

                let len = fields.len();

                let arr_var = Exp::var(id.clone());
                let arr_elts =
                    Exp::RecField { record: arr_var.clone().boxed(), label: "elts".into() };

                istmts.push(IntermediateStmt::Any(id.clone(), ty.clone()));
                let mut assumptions = fields
                    .into_iter()
                    .enumerate()
                    .map(|(ix, f)| {
                        Exp::qvar("Seq.get".into())
                            .app([arr_elts.clone(), Exp::Const(Constant::Int(ix as i128, None))])
                            .eq(f.to_why(lower, istmts))
                    })
                    .chain([Exp::qvar("Seq.length".into())
                        .app([arr_elts.clone()])
                        .eq(Exp::Const(Constant::Int(len as i128, None)))])
                    .reduce(Exp::log_and)
                    .expect("array literal missing assumption");
                assumptions.reassociate();

                istmts.push(IntermediateStmt::Assume(assumptions));
                Exp::var(id)
            }
            RValue::Repeat(e, len) => {
                let args = [
                    Arg::Ty(lower.ty(e.ty(lower.ctx.tcx, lower.locals))),
                    Arg::Term(len.to_why(lower, istmts)),
                    Arg::Term(Exp::Lam(
                        Box::new([Binder::wild(int_ty(lower.ctx, lower.names))]),
                        e.to_why(lower, istmts).boxed(),
                    )),
                ];

                istmts.push(IntermediateStmt::call(
                    "_res".into(),
                    lower.ty(ty),
                    lower.names.in_pre(PreMod::Slice, "create"),
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
                            op = op.field("current".into())
                        }
                        Exp::qvar(lower.names.in_pre(PreMod::Slice, "length")).app([op])
                    }
                    TyKind::RawPtr(ty, _) => {
                        assert!(ty.is_slice());
                        Exp::qvar(lower.names.in_pre(PreMod::Slice, "slice_ptr_len"))
                            .app([op.to_why(lower, istmts)])
                    }
                    _ => unreachable!(),
                }
            }
            RValue::Ptr(pl) => {
                istmts.push(IntermediateStmt::call(
                    "_ptr".into(),
                    lower.ty(ty),
                    lower.names.in_pre(PreMod::Opaque, "fresh_ptr"),
                    [],
                ));

                if pl.ty(lower.ctx.tcx, lower.locals).is_slice() {
                    let lhs = Exp::qvar(lower.names.in_pre(PreMod::Slice, "slice_ptr_len"))
                        .app([Exp::qvar("_ptr".into())]);
                    let rhs = Exp::qvar(lower.names.in_pre(PreMod::Slice, "length"))
                        .app([rplace_to_expr(lower, &pl, istmts)]);
                    istmts.push(IntermediateStmt::Assume(lhs.eq(rhs)));
                }

                Exp::var("_ptr")
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
    ) -> (Vec<IntermediateStmt>, Expr) {
        let mut istmts = vec![];
        match self {
            Terminator::Goto(bb) => (istmts, Expr::Symbol(format!("bb{}", bb.as_usize()).into())),
            Terminator::Switch(switch, branches) => {
                let ty = switch.ty(lower.ctx.tcx, lower.locals);
                let discr = switch.to_why(lower, &mut istmts);
                (istmts, branches.to_why(lower.ctx, lower.names, discr, &ty))
            }
            Terminator::Return => {
                (istmts, Expr::Symbol("return".into()).app([Arg::Term(Exp::var("_0"))]))
            }
            Terminator::Abort(span) => {
                let mut exp = Exp::mk_false();
                if let Some(attr) = lower.names.span(span) {
                    exp = exp.with_attr(attr);
                };
                (istmts, Expr::assert(exp, Expr::Any))
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
    ) -> Expr {
        match self {
            Branches::Int(brs, def) => {
                let TyKind::Int(ity) = discr_ty.kind() else {
                    panic!("Branches::Int try to evaluate a type that is not Int")
                };
                let brs = mk_switch_branches(
                    discr,
                    brs.into_iter().map(|(mut val, tgt)| {
                        let why_ty =
                            Type::TConstructor(names.in_pre(ity_to_prelude(ctx.tcx, *ity), "t"));
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
                    }),
                );
                let brs = brs.chain([Defn::simple("default", mk_goto(def).black_box())]);
                Expr::Defn(Expr::Any.boxed(), false, brs.collect())
            }
            Branches::Uint(brs, def) => {
                let uty = match discr_ty.kind() {
                    TyKind::Uint(uty) => uty,
                    _ => panic!("Branches::Uint try to evaluate a type that is not Uint"),
                };

                let brs = mk_switch_branches(
                    discr,
                    brs.into_iter().map(|(val, tgt)| {
                        let why_ty =
                            Type::TConstructor(names.in_pre(uty_to_prelude(ctx.tcx, *uty), "t"));
                        let e = Exp::Const(Constant::Uint(val, Some(why_ty)));
                        (e, mk_goto(tgt))
                    }),
                )
                .chain([Defn::simple("default", mk_goto(def).black_box())])
                .collect();
                Expr::Defn(Expr::Any.boxed(), false, brs)
            }
            Branches::Constructor(adt, substs, vars, def) => {
                let brs = mk_adt_switch(ctx, names, adt, substs, discr, vars, def);
                Expr::Defn(Expr::Any.boxed(), false, brs)
            }
            Branches::Bool(f, t) => {
                let brs = mk_switch_branches(discr, vec![
                    (Exp::mk_false(), mk_goto(f)),
                    (Exp::mk_true(), mk_goto(t)),
                ]);

                Expr::Defn(Expr::Any.boxed(), false, brs.collect())
            }
        }
    }
}

fn mk_goto(bb: BasicBlock) -> Expr {
    Expr::Symbol(format!("bb{}", bb.as_u32()).into())
}

fn mk_adt_switch<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    adt: AdtDef<'tcx>,
    subst: GenericArgsRef<'tcx>,
    discr: Exp,
    brch: Box<[(VariantIdx, BasicBlock)]>,
    default: Option<BasicBlock>,
) -> Box<[Defn]> {
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

            let (params, ids): (Vec<_>, Vec<_>) = var
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
            let body = Expr::assert(discr.clone().eq(body), mk_goto(tgt).black_box());
            let name = format!("br{}", ix.as_usize()).into();

            Defn { name, body, params: params.into(), attrs: vec![] }
        })
        .collect();
    assert!(brch.next().is_none());
    res
}

fn mk_switch_branches(
    discr: Exp,
    brch: impl IntoIterator<Item = (Exp, Expr)>,
) -> impl Iterator<Item = Defn> {
    brch.into_iter().enumerate().map(move |(ix, (cond, tgt))| {
        let filter = Expr::assert(discr.clone().eq(cond), tgt.black_box());
        Defn::simple(format!("br{ix}"), filter)
    })
}

impl<'tcx> Block<'tcx> {
    pub(crate) fn to_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        id: BasicBlock,
    ) -> Defn {
        let (istmts, terminator) = self.terminator.to_why(lower);

        let mut statements = vec![];

        for (ix, s) in self.stmts.into_iter().enumerate() {
            let stmt = s.to_why(lower);

            let body = assemble_intermediates(
                stmt.into_iter(),
                Expr::Symbol(format!("s{}", ix + 1).into()),
            );
            statements.push(Defn::simple(format!("s{}", ix), body));
        }

        let body = assemble_intermediates(istmts.into_iter(), terminator);
        statements.push(Defn::simple(format!("s{}", statements.len()), body));

        let mut body = Expr::Symbol("s0".into());
        if !self.invariants.is_empty() {
            body = body.black_box();
        }

        for i in self.invariants.into_iter().rev() {
            body = Expr::assert(
                lower_pure(lower.ctx, lower.names, &i.body).with_attr(Attribute::Attr(i.expl)),
                body,
            );
        }

        body = body.where_(statements.into());

        Defn::simple(format!("bb{}", id.as_usize()), body)
    }
}

fn assemble_intermediates<I>(istmts: I, exp: Expr) -> Expr
where
    I: IntoIterator<Item = IntermediateStmt>,
    I: DoubleEndedIterator<Item = IntermediateStmt>,
{
    istmts.rfold(exp, |tail, stmt| match stmt {
        IntermediateStmt::Assign(id, exp) => tail.assign(id, exp),
        IntermediateStmt::Call(params, fun, args) => Expr::Symbol(fun)
            .app(args.into_iter().chain([Arg::Cont(Expr::Lambda(params, tail.boxed()))])),
        IntermediateStmt::Assume(e) => Expr::assume(e, tail),
        IntermediateStmt::Assert(e) => Expr::assert(e, tail),
        IntermediateStmt::Any(id, ty) => Expr::Defn(
            Expr::Any.boxed(),
            false,
            Box::new([Defn {
                name: "any_".into(),
                attrs: vec![],
                params: Box::new([Param::Term(id, ty)]),
                body: tail.black_box(),
            }]),
        ),
    })
}

pub(crate) fn borrow_generated_id<'tcx, V: Debug, N: Namer<'tcx>>(
    names: &N,
    original_borrow: Exp,
    projections: &[ProjectionElem<V, Ty<'tcx>>],
    mut translate_index: impl FnMut(&V) -> Exp,
) -> Exp {
    let mut borrow_id = Exp::qvar(names.in_pre(PreMod::MutBor, "get_id")).app([original_borrow]);
    for proj in projections {
        match proj {
            ProjectionElem::Deref => {
                // TODO: If this is a deref of a mutable borrow, the id should change !
            }
            ProjectionElem::Field(idx, _) => {
                borrow_id = Exp::qvar(names.in_pre(PreMod::MutBor, "inherit_id"))
                    .app([borrow_id, Exp::Const(Constant::Int(idx.as_u32() as i128 + 1, None))]);
            }
            ProjectionElem::Index(x) => {
                borrow_id = Exp::qvar(names.in_pre(PreMod::MutBor, "inherit_id"))
                    .app([borrow_id, translate_index(x)]);
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
    Call(Box<[Param]>, QName, Box<[Arg]>),
    // -{ E }- K
    Assume(Exp),
    // { E } K
    Assert(Exp),

    Any(Ident, Type),
}

impl IntermediateStmt {
    fn call(id: Ident, ty: Type, f: QName, args: impl IntoIterator<Item = Arg>) -> Self {
        IntermediateStmt::Call(Box::new([Param::Term(id, ty)]), f, args.into_iter().collect())
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

                let func = lower.names.in_pre(PreMod::MutBor, match bor_kind {
                    BorrowKind::Mut => "borrow_mut",
                    BorrowKind::Final(_) => "borrow_final",
                });

                let bor_id_arg;
                let rhs_rplace;
                let rhs_constr;

                if let BorrowKind::Final(deref_index) = bor_kind {
                    let (original_borrow_ty, original_borrow, original_borrow_constr) =
                        projections_to_expr(
                            lower,
                            &mut istmts,
                            rhs_local_ty,
                            Focus::new(|_| Exp::var(ident_of(rhs.local))),
                            Box::new(|_, x| x),
                            &rhs.projection[..deref_index],
                        );
                    let (_, foc, constr) = projections_to_expr(
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
                            Exp::qvar(
                                lower
                                    .names
                                    .in_pre(uty_to_prelude(lower.ctx.tcx, UintTy::Usize), "t'int"),
                            )
                            .app([Exp::var(ident_of(*sym))])
                        },
                    );

                    bor_id_arg = Some(Arg::Term(borrow_id));
                } else {
                    let (_, foc, constr) = projections_to_expr(
                        &lower,
                        &mut istmts,
                        rhs_local_ty,
                        Focus::new(|_| Exp::var(ident_of(rhs.local))),
                        Box::new(|_, x| x),
                        &rhs.projection,
                    );
                    rhs_rplace = foc.call(&mut istmts);
                    rhs_constr = constr;
                    bor_id_arg = None;
                }

                if let Some(ref rhs_inv_fun) = rhs_inv_fun {
                    istmts.push(IntermediateStmt::Assert(
                        rhs_inv_fun.clone().app([rhs_rplace.clone()]),
                    ));
                }

                let args =
                    [Arg::Ty(rhs_ty_low), Arg::Term(rhs_rplace)].into_iter().chain(bor_id_arg);

                let borrow_call = IntermediateStmt::call("_ret'".into(), lhs_ty_low, func, args);
                istmts.push(borrow_call);
                lower.assignment(&lhs, Exp::var("_ret'"), &mut istmts);

                let reassign = Exp::var("_ret'").field("final".into());

                if let Some(rhs_inv_fun) = rhs_inv_fun {
                    istmts.push(IntermediateStmt::Assume(rhs_inv_fun.app([reassign.clone()])));
                }

                let new_rhs = rhs_constr(&mut istmts, reassign);
                istmts.push(IntermediateStmt::Assign(Ident::build(rhs.local.as_str()), new_rhs));
            }
            Statement::Assignment(lhs, e, _span) => {
                let rhs = e.to_why(lower, lhs.ty(lower.ctx.tcx, lower.locals), &mut istmts);
                lower.assignment(&lhs, rhs, &mut istmts);
            }
            Statement::Call(dest, fun_id, subst, args, _) => {
                let (fun_qname, args) = func_call_to_why3(lower, fun_id, subst, args, &mut istmts);
                let ty = dest.ty(lower.ctx.tcx, lower.locals);
                let ty = lower.ty(ty);

                istmts.push(IntermediateStmt::call("_ret'".into(), ty, fun_qname, args));
                lower.assignment(&dest, Exp::var("_ret'"), &mut istmts);
            }
            Statement::Resolve { did, subst, pl } => {
                let rp = Exp::qvar(lower.names.item(did, subst));
                let loc = pl.local;

                let bound = lower.fresh_sym_from("x");

                let pat = pattern_of_place(lower.ctx.tcx, lower.locals, pl, bound);

                let pat = lower_pat(lower.ctx, lower.names, &pat);
                let exp = if let WPattern::VarP(_) = pat {
                    rp.app([Exp::var(ident_of(loc))])
                } else {
                    Exp::var(ident_of(loc)).match_([
                        (pat, rp.app([Exp::var(bound.as_str())])),
                        (WPattern::Wildcard, Exp::mk_true()),
                    ])
                };

                istmts.push(IntermediateStmt::Assume(exp));
            }
            Statement::Assertion { cond, msg, trusted } => {
                let e = lower_pure(lower.ctx, lower.names, &cond).with_attr(Attribute::Attr(msg));
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
                let exp = if let WPattern::VarP(_) = pat {
                    inv_fun.app([Exp::var(ident_of(loc))])
                } else {
                    Exp::var(ident_of(loc)).match_([
                        (pat, inv_fun.app([Exp::var(bound.as_str())])),
                        (WPattern::Wildcard, Exp::mk_true()),
                    ])
                };

                let exp = exp.with_attr(Attribute::Attr(format!("expl:type invariant")));
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
    locals: &LocalDecls<'tcx>,
    pl: Place<'tcx>,
    binder: Symbol,
) -> Pattern<'tcx> {
    let mut pat = Pattern::Binder(binder);

    for (pl, el) in pl.iter_projections().rev() {
        let ty = pl.ty(tcx, locals);
        match el {
            ProjectionElem::Deref => match ty.ty.kind() {
                TyKind::Ref(_, _, mutbl) => match mutbl {
                    Mutability::Not => {
                        pat = Pattern::Deref { pointee: Box::new(pat), kind: PointerKind::Shr }
                    }
                    Mutability::Mut => {
                        pat = Pattern::Deref { pointee: Box::new(pat), kind: PointerKind::Mut }
                    }
                },
                _ if ty.ty.is_box() => {
                    pat = Pattern::Deref { pointee: Box::new(pat), kind: PointerKind::Box }
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
                    let mut fields: Box<_> = repeat_n(Pattern::Wildcard, fields_len).collect();
                    fields[fidx.as_usize()] = pat;
                    pat = Pattern::Constructor { variant, substs, fields }
                }
                TyKind::Tuple(tys) => {
                    let mut fields: Box<_> = repeat_n(Pattern::Wildcard, tys.len()).collect();
                    fields[fidx.as_usize()] = pat;
                    pat = Pattern::Tuple(fields)
                }
                TyKind::Closure(did, substs) => {
                    let mut fields: Box<_> =
                        repeat_n(Pattern::Wildcard, substs.as_closure().upvar_tys().len())
                            .collect();
                    fields[fidx.as_usize()] = pat;
                    pat = Pattern::Constructor { variant: *did, substs, fields }
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
    args: Box<[Operand<'tcx>]>,
    istmts: &mut Vec<IntermediateStmt>,
) -> (QName, Box<[Arg]>) {
    // TODO(xavier): Perform this simplification earlier
    // Eliminate "rust-call" ABI
    let args: Box<[_]> = if lower.ctx.is_closure_like(id) {
        assert!(args.len() == 2, "closures should only have two arguments (env, args)");
        let [arg, Operand::Move(pl)] = *args.into_array().unwrap() else { panic!() };

        let real_sig = lower.ctx.signature_unclosure(subst.as_closure().sig(), Safety::Safe);

        once(Arg::Term(arg.to_why(lower, istmts)))
            .chain(real_sig.inputs().skip_binder().iter().enumerate().map(|(ix, inp)| {
                let projection = pl
                    .projection
                    .iter()
                    .copied()
                    .chain([ProjectionElem::Field(ix.into(), *inp)])
                    .collect();
                Arg::Term(Operand::Move(Place { projection, ..pl }).to_why(lower, istmts))
            }))
            .collect()
    } else {
        args.into_iter().map(|a| a.to_why(lower, istmts)).map(|a| Arg::Term(a)).collect()
    };

    (lower.names.item(id, subst), args)
}
