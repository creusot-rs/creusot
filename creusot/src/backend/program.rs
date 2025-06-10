//! This module translates [FMIR](crate::translation::fmir) programs to why3.
//!
//! Each `into_why` function in this module translates a specific FMIR structure. These
//! functions may take a `istmts` parameter of type [`&mut Vec<IntermediateStmt>`](IntermediateStmt),
//! because one FMIR statement may correspond to a coma expression with multiple steps.
//!
//! They also take a [`lower: &mut LoweringState<'_, 'tcx, N>`](LoweringState) that is in
//! charge of avoiding naming conficts (very much needed, since we generate additional
//! intermediate variables here) and carrying the context (for e.g. typing information).

use crate::{
    backend::{
        Why3Generator,
        clone_map::{Namer, PreMod},
        dependency::Dependency,
        is_trusted_item,
        optimization::{gather_usage, infer_proph_invariants, simplify_fmir},
        projections::{Focus, borrow_generated_id, projections_to_expr},
        signature::lower_program_sig,
        term::{lower_pat, lower_pure},
        ty::{
            constructor, floatty_to_prelude, int_ty, ity_to_prelude, translate_ty, ty_to_prelude,
            uty_to_prelude,
        },
        wto::{Component, weak_topological_order},
    },
    ctx::{BodyId, Dependencies},
    naming::name,
    translated_item::FileModule,
    translation::{
        fmir::{
            Block, Body, BorrowKind, Branches, LocalDecls, Operand, Place, RValue, Statement,
            Terminator, TrivialInv,
        },
        pearlite::Pattern,
    },
};
use indexmap::IndexMap;
use petgraph::graphmap::DiGraphMap;
use rustc_hir::{
    Safety,
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{BasicBlock, BinOp, ProjectionElem, START_BLOCK, UnOp, tcx::PlaceTy},
    ty::{AdtDef, GenericArgsRef, Ty, TyCtxt, TyKind},
};
use rustc_span::DUMMY_SP;
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{IntTy, UintTy};
use std::{collections::HashMap, fmt::Debug, iter::once};
use why3::{
    Ident, Name,
    coma::{Arg, Defn, Expr, IsRef, Param, Prototype, Term, Var},
    declaration::{Attribute, Condition, Contract, Decl, Meta, MetaArg, MetaIdent, Module},
    exp::{Binder, Constant, Exp, Pattern as WPattern},
    ty::Type,
};

pub(crate) fn translate_function(ctx: &Why3Generator, def_id: DefId) -> Option<FileModule> {
    let names = Dependencies::new(ctx, def_id);

    if !def_id.is_local() || !ctx.has_body(def_id) || is_trusted_item(ctx.tcx, def_id) {
        return None;
    }

    let name = names.item_ident(names.self_id, names.self_subst);
    let body = Decl::Coma(to_why(ctx, &names, name, BodyId::new(def_id.expect_local(), None)));

    let mut decls = names.provide_deps(ctx);
    decls.push(Decl::Meta(Meta {
        name: MetaIdent::String("compute_max_steps".into()),
        args: [MetaArg::Integer(1_000_000)].into(),
    }));
    decls.push(body);

    let attrs = ctx.span_attr(ctx.def_span(def_id)).into_iter().collect();
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Some(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } })
}

pub(crate) fn val(
    sig: Prototype,
    contract: Contract,
    return_ident: Ident,
    return_ty: why3::ty::Type,
) -> Decl {
    let requires = contract.requires.into_iter().map(Condition::labelled_exp);
    let body = requires.rfold(Expr::Any, |acc, cond| Expr::assert(cond, acc));

    let mut postcond = Expr::var(return_ident).app([Arg::Term(Exp::var(name::result()))]);
    postcond = postcond.black_box();
    let ensures = contract.ensures.into_iter().map(Condition::unlabelled_exp);
    postcond = ensures.rfold(postcond, |acc, cond| Expr::assert(cond, acc));

    let body = Expr::Defn(
        body.boxed(),
        false,
        [Defn {
            prototype: Prototype {
                name: return_ident.refresh(), // not used in the body
                attrs: vec![],
                params: [Param::Term(name::result(), return_ty)].into(),
            },
            body: postcond,
        }]
        .into(),
    );
    Decl::Coma(Defn { prototype: Prototype { attrs: Vec::new(), ..sig }, body })
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

/// Translate a program function body to why3.
pub(crate) fn to_why<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    body_id: BodyId,
) -> Defn {
    // The function receives `outer_return` as an argument handler and
    // defines the `inner_return` that wraps `outer_return` with the postcondition:
    //
    // let rec f ... outer_return =
    //   ... inner_return result ...
    //   [ inner_return x -> {postcondition} (! outer_return x ) ]
    let outer_return = Ident::fresh_local("return");
    let inner_return = outer_return.refresh();

    let mut body = ctx.fmir_body(body_id).clone();
    let block_idents: IndexMap<BasicBlock, Ident> = body
        .blocks
        .iter()
        .map(|(blk, _)| (*blk, Ident::fresh_local(format!("bb{}", blk.as_usize()))))
        .collect();

    // Remember the index of every argument before removing unused variables in simplify_fmir
    let arg_index = body
        .locals
        .iter()
        .flat_map(|(id, decl)| if decl.arg { Some(*id) } else { None })
        .enumerate()
        .map(|(i, k)| (k, i))
        .collect::<HashMap<_, _>>();

    simplify_fmir(gather_usage(&body), &mut body);

    let wto = weak_topological_order(&node_graph(&body), START_BLOCK);
    infer_proph_invariants(ctx, &mut body);

    let blocks: Box<[Defn]> = wto
        .into_iter()
        .map(|c| {
            component_to_defn(&mut body, ctx, names, body_id.def_id, &block_idents, inner_return, c)
        })
        .collect();

    let (mut sig, contract, return_ty) = if body_id.promoted.is_none() {
        let def_id = body_id.def_id();
        let typing_env = ctx.typing_env(def_id);
        let mut pre_sig = ctx.sig(def_id).clone().normalize(ctx.tcx, typing_env);
        pre_sig.add_type_invariant_spec(ctx, def_id, typing_env);
        lower_program_sig(ctx, names, name, pre_sig, def_id, outer_return)
    } else {
        let ret = body.locals.first().map(|(_, decl)| decl.clone()).unwrap();
        let ret_ty = translate_ty(ctx, names, ret.span, ret.ty);
        (
            Prototype {
                name,
                attrs: vec![],
                params: [Param::Cont(
                    outer_return,
                    [].into(),
                    [Param::Term(Ident::fresh_local("x"), ret_ty.clone())].into(), // argument that has to be named for useless reasons (difficult to fix in Coma/Why3 parser)
                )]
                .into(),
            },
            Contract::default(),
            ret_ty,
        )
    };
    // Bind local variables in the body
    let vars: Box<[_]> = body
        .locals
        .into_iter()
        .map(|(id, decl)| {
            let ty = translate_ty(ctx, names, decl.span, decl.ty);
            let init = if decl.arg {
                let (id2, ty2) = sig.params[arg_index[&id]].as_term();
                assert_eq! {ty, *ty2};
                Exp::var(id2)
            } else {
                Exp::qvar(names.in_pre(PreMod::Any, "any_l")).app([Exp::unit()])
            };
            Var(id, ty.clone(), init, IsRef::Ref)
        })
        .collect();

    let mut body = Expr::Defn(Expr::var(block_idents[0]).boxed(), true, blocks);

    let inferred_closure_spec = ctx.is_closure_like(body_id.def_id())
        && !ctx.sig(body_id.def_id()).contract.has_user_contract;

    // We remove the barrier around the definition in the following edge cases:
    let open_body =
        // a closure with no contract
        inferred_closure_spec
        // a promoted item
        || body_id.promoted.is_some();

    let ensures = contract.ensures.into_iter().map(Condition::labelled_exp);
    let mut postcond = Expr::var(outer_return).app([Arg::Term(Exp::var(name::result()))]);
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
        [Defn {
            prototype: Prototype {
                name: inner_return,
                attrs: vec![],
                params: [Param::Term(name::result(), return_ty)].into(),
            },
            body: postcond,
        }]
        .into(),
    );

    let requires = contract.requires.into_iter().map(Condition::labelled_exp);
    if !open_body {
        body = requires.rfold(body, |acc, req| Expr::assert(req, acc));
    }
    Defn { prototype: sig, body }
}

fn component_to_defn<'tcx, N: Namer<'tcx>>(
    body: &mut Body<'tcx>,
    ctx: &Why3Generator<'tcx>,
    names: &N,
    def_id: LocalDefId,
    block_idents: &IndexMap<BasicBlock, Ident>,
    return_ident: Ident,
    c: Component<BasicBlock>,
) -> Defn {
    let mut lower =
        LoweringState { ctx, names, locals: &body.locals, def_id, block_idents, return_ident };
    let (head, tl) = match c {
        Component::Vertex(v) => {
            let block = body.blocks.shift_remove(&v).unwrap();
            return block.into_why(&mut lower, v);
        }
        Component::Component(v, tls) => (v, tls),
    };

    let block = body.blocks.shift_remove(&head).unwrap();
    let mut block = block.into_why(&mut lower, head);

    let defns = tl
        .into_iter()
        .map(|id| component_to_defn(body, ctx, names, def_id, block_idents, return_ident, id))
        .collect();

    if !block.body.is_guarded() {
        block.body = block.body.black_box();
    }

    let inner = Expr::Defn(block.body.boxed(), true, defns);
    block.body = Expr::Defn(
        Expr::var(block.prototype.name).boxed(),
        true,
        [Defn::simple(block.prototype.name, inner)].into(),
    );
    block
}

pub(crate) struct LoweringState<'a, 'tcx, N: Namer<'tcx>> {
    pub(super) ctx: &'a Why3Generator<'tcx>,
    pub(super) names: &'a N,
    pub(super) locals: &'a LocalDecls<'tcx>,
    pub(super) def_id: LocalDefId,
    block_idents: &'a IndexMap<BasicBlock, Ident>,
    return_ident: Ident,
}

impl<'tcx, N: Namer<'tcx>> LoweringState<'_, 'tcx, N> {
    pub(super) fn ty(&self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, DUMMY_SP, ty)
    }

    fn assignment(&self, lhs: &Place<'tcx>, rhs: Term, istmts: &mut Vec<IntermediateStmt>) {
        let local_ty = PlaceTy::from_ty(self.locals[&lhs.local].ty);
        let (_, _, constructor) = projections_to_expr(
            self.ctx,
            self.names,
            Some(istmts),
            local_ty,
            Focus::new(|_| Exp::var(lhs.local)),
            Box::new(|_, x| x),
            &lhs.projections,
            |ix| Exp::var(*ix),
        );

        let rhs = constructor(Some(istmts), rhs);
        istmts.push(IntermediateStmt::Assign(lhs.local, rhs));
    }

    fn rplace_to_expr(&self, pl: &Place<'tcx>, istmts: &mut Vec<IntermediateStmt>) -> Exp {
        let local_ty = PlaceTy::from_ty(self.locals[&pl.local].ty);
        let (_, rhs, _) = projections_to_expr(
            self.ctx,
            self.names,
            Some(istmts),
            local_ty,
            Focus::new(|_| Exp::var(pl.local)),
            Box::new(|_, _| unreachable!()),
            &pl.projections,
            |ix| Exp::var(*ix),
        );
        rhs.call(Some(istmts))
    }
}

impl<'tcx> Operand<'tcx> {
    fn into_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> Exp {
        match self {
            Operand::Move(pl) | Operand::Copy(pl) => lower.rplace_to_expr(&pl, istmts),
            Operand::Constant(c) => lower_pure(lower.ctx, lower.names, &c),
            Operand::Promoted(pid, ty) => {
                let var = Ident::fresh_local(format!("pr{}", pid.as_usize()));
                istmts.push(IntermediateStmt::call(
                    var,
                    lower.ty(ty),
                    Name::local(lower.names.promoted(lower.def_id, pid)),
                    [],
                ));
                Exp::var(var)
            }
        }
    }
}

impl<'tcx> RValue<'tcx> {
    /// Translate a `RValue` from FMIR to Why3.
    fn into_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        ty: Ty<'tcx>,
        istmts: &mut Vec<IntermediateStmt>,
    ) -> Exp {
        match self {
            RValue::Operand(op) => op.into_why(lower, istmts),
            RValue::BinOp(op, l, r) => {
                let l_ty = l.ty(lower.ctx.tcx, lower.locals);

                match (op, l_ty.kind()) {
                    (_, TyKind::Float(_)) => (),
                    (BinOp::Eq, _) => {
                        return l.into_why(lower, istmts).eq(r.into_why(lower, istmts));
                    }
                    (BinOp::Ne, _) => {
                        return l.into_why(lower, istmts).neq(r.into_why(lower, istmts));
                    }
                    _ => (),
                }

                let prelude = ty_to_prelude(lower.ctx.tcx, l_ty.kind());

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
                        Exp::qvar(qname).app([r.into_why(lower, istmts)])
                    }
                    _ => r.into_why(lower, istmts),
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
                let args = [l.into_why(lower, istmts), r];

                if logic {
                    Exp::qvar(fname).app(args)
                } else {
                    let ret_ident = Ident::fresh_local("_ret");
                    istmts.push(IntermediateStmt::call(
                        ret_ident,
                        lower.ty(ty),
                        Name::Global(fname),
                        args.map(Arg::Term),
                    ));
                    Exp::var(ret_ident)
                }
            }
            RValue::UnaryOp(UnOp::Not, arg) => {
                let a_ty = arg.ty(lower.ctx.tcx, lower.locals);
                match a_ty.kind() {
                    TyKind::Bool => arg.into_why(lower, istmts).not(),
                    TyKind::Int(_) | TyKind::Uint(_) => {
                        let prelude: PreMod = match a_ty.kind() {
                            TyKind::Int(ity) => ity_to_prelude(lower.ctx.tcx, *ity),
                            TyKind::Uint(uty) => uty_to_prelude(lower.ctx.tcx, *uty),
                            _ => unreachable!("this is not an executable path {ty:?}"),
                        };

                        Exp::qvar(lower.names.in_pre(prelude, "bw_not"))
                            .app(vec![arg.into_why(lower, istmts)])
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
                let ret_ident = Ident::fresh_local("_ret");
                let arg = Arg::Term(arg.into_why(lower, istmts));
                istmts.push(IntermediateStmt::call(ret_ident, lower.ty(ty), Name::Global(neg), [
                    arg,
                ]));
                Exp::var(ret_ident)
            }
            RValue::Constructor(id, subst, args) => {
                if lower.ctx.def_kind(id) == DefKind::Closure {
                    lower.names.dependency(Dependency::Item(id, subst));
                }
                let args = args.into_iter().map(|a| a.into_why(lower, istmts)).collect();
                constructor(lower.names, args, id, subst)
            }
            RValue::Tuple(flds) if flds.is_empty() => Exp::unit(),
            RValue::Tuple(flds) if flds.len() == 1 => {
                flds.into_iter().next().unwrap().into_why(lower, istmts)
            }
            RValue::Tuple(flds) => {
                let TyKind::Tuple(tys) = ty.kind() else { unreachable!() };
                Exp::Record {
                    fields: flds
                        .into_iter()
                        .enumerate()
                        .map(|(ix, f)| {
                            (
                                Name::local(lower.names.tuple_field(tys, ix.into())),
                                f.into_why(lower, istmts),
                            )
                        })
                        .collect(),
                }
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
                        let arg = e.into_why(lower, istmts);
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
                        let to_exp = Exp::qvar(to_fname).app(vec![e.into_why(lower, istmts)]);

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
                        let of_ret_id = Ident::fresh_local("_ret_from");
                        istmts.push(IntermediateStmt::call(
                            of_ret_id,
                            lower.ty(ty),
                            Name::Global(of_fname),
                            [Arg::Term(to_exp)],
                        ));
                        Exp::var(of_ret_id)
                    }
                }
            }
            RValue::Len(op) => Exp::qvar(lower.names.in_pre(PreMod::Slice, "length"))
                .app([op.into_why(lower, istmts)]),
            RValue::Array(fields) => {
                let id = Ident::fresh_local("__arr_temp");
                let ty = lower.ty(ty);

                let len = fields.len();

                let record = Exp::var(id).boxed();
                let label = Name::Global(lower.names.in_pre(PreMod::Slice, "elts"));
                let arr_elts = Exp::RecField { record, label };

                istmts.push(IntermediateStmt::Any(id, ty.clone()));
                let mut assumptions = fields
                    .into_iter()
                    .enumerate()
                    .map(|(ix, f)| {
                        Exp::qvar(name::seq_get())
                            .app([arr_elts.clone(), Exp::Const(Constant::Int(ix as i128, None))])
                            .eq(f.into_why(lower, istmts))
                    })
                    .chain([Exp::qvar(name::seq_length())
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
                    Arg::Term(len.into_why(lower, istmts)),
                    Arg::Term(Exp::Lam(
                        [Binder::wild(int_ty(lower.ctx, lower.names))].into(),
                        e.into_why(lower, istmts).boxed(),
                    )),
                ];
                let res_ident = Ident::fresh_local("_res");
                istmts.push(IntermediateStmt::call(
                    res_ident,
                    lower.ty(ty),
                    Name::Global(lower.names.in_pre(PreMod::Slice, "create")),
                    args,
                ));

                Exp::var(res_ident)
            }
            RValue::Snapshot(t) => lower_pure(lower.ctx, lower.names, &t),
            RValue::Borrow(_, _, _) => unreachable!(), // Handled in Statement::to_why
            RValue::UnaryOp(UnOp::PtrMetadata, op) => {
                match op.ty(lower.ctx.tcx, lower.locals).kind() {
                    TyKind::Ref(_, ty, mu) => {
                        assert!(ty.is_slice());
                        let mut op = op.into_why(lower, istmts);
                        if mu.is_mut() {
                            op = op.field(Name::Global(name::current()))
                        }
                        Exp::qvar(lower.names.in_pre(PreMod::Slice, "length")).app([op])
                    }
                    TyKind::RawPtr(ty, _) => {
                        assert!(ty.is_slice());
                        Exp::qvar(lower.names.in_pre(PreMod::Slice, "slice_ptr_len"))
                            .app([op.into_why(lower, istmts)])
                    }
                    _ => unreachable!(),
                }
            }
            RValue::Ptr(pl) => {
                let ptr_ident = Ident::fresh_local("_ptr");
                istmts.push(IntermediateStmt::call(
                    ptr_ident,
                    lower.ty(ty),
                    Name::Global(lower.names.in_pre(PreMod::Opaque, "fresh_ptr")),
                    [],
                ));

                if pl.ty(lower.ctx.tcx, lower.locals).is_slice() {
                    let lhs = Exp::qvar(lower.names.in_pre(PreMod::Slice, "slice_ptr_len"))
                        .app([Exp::var(ptr_ident)]); // TODO This was not caught by the test suite
                    let rhs = Exp::qvar(lower.names.in_pre(PreMod::Slice, "length"))
                        .app([lower.rplace_to_expr(&pl, istmts)]);
                    istmts.push(IntermediateStmt::Assume(lhs.eq(rhs)));
                }

                Exp::var(ptr_ident)
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

    fn into_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
    ) -> (Vec<IntermediateStmt>, Expr) {
        let mut istmts = vec![];
        let exp = match self {
            Terminator::Goto(bb) => Expr::var(*lower.block_idents.get(&bb).unwrap()),
            Terminator::Switch(switch, branches) => {
                let ty = switch.ty(lower.ctx.tcx, lower.locals);
                let discr = switch.into_why(lower, &mut istmts);
                branches.into_why(lower, discr, &ty)
            }
            Terminator::Return => {
                let p = *lower.locals.get_index(0).unwrap().0;
                Expr::var(lower.return_ident).app([Arg::Term(Exp::var(p))])
            }
            Terminator::Abort(span) => {
                let mut exp = Exp::mk_false();
                if let Some(attr) = lower.names.span(span) {
                    exp = exp.with_attr(attr);
                };
                Expr::assert(exp, Expr::Any)
            }
        };
        (istmts, exp)
    }
}

impl<'tcx> Branches<'tcx> {
    fn into_why<N: Namer<'tcx>>(
        self,
        lower: &LoweringState<'_, 'tcx, N>,
        discr: Exp,
        discr_ty: &Ty<'tcx>,
    ) -> Expr {
        let LoweringState { ctx, names, block_idents, .. } = *lower;
        match self {
            Branches::Int(brs, def) => {
                let TyKind::Int(ity) = discr_ty.kind() else {
                    panic!("Branches::Int try to evaluate a type that is not Int")
                };
                let brs = mk_switch_branches(
                    discr,
                    brs.into_iter().map(|(mut val, tgt)| {
                        let why_ty =
                            Type::qconstructor(names.in_pre(ity_to_prelude(ctx.tcx, *ity), "t"));
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
                        (e, mk_goto(block_idents, tgt))
                    }),
                );
                let brs = brs.chain([Defn::simple(
                    Ident::fresh_local("default"),
                    mk_goto(block_idents, def).black_box(),
                )]);
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
                            Type::qconstructor(names.in_pre(uty_to_prelude(ctx.tcx, *uty), "t"));
                        let e = Exp::Const(Constant::Uint(val, Some(why_ty)));
                        (e, mk_goto(block_idents, tgt))
                    }),
                )
                .chain([Defn::simple(
                    Ident::fresh_local("default"),
                    mk_goto(block_idents, def).black_box(),
                )])
                .collect();
                Expr::Defn(Expr::Any.boxed(), false, brs)
            }
            Branches::Constructor(adt, substs, vars, def) => {
                let brs = mk_adt_switch(lower, adt, substs, discr, vars, def);
                Expr::Defn(Expr::Any.boxed(), false, brs)
            }
            Branches::Bool(f, t) => {
                let brs = mk_switch_branches(discr, vec![
                    (Exp::mk_false(), mk_goto(block_idents, f)),
                    (Exp::mk_true(), mk_goto(block_idents, t)),
                ]);

                Expr::Defn(Expr::Any.boxed(), false, brs.collect())
            }
        }
    }
}

fn mk_goto(block_idents: &IndexMap<BasicBlock, Ident>, bb: BasicBlock) -> Expr {
    Expr::var(*block_idents.get(&bb).unwrap())
}

fn mk_adt_switch<'tcx, N: Namer<'tcx>>(
    lower: &LoweringState<'_, 'tcx, N>,
    adt: AdtDef<'tcx>,
    subst: GenericArgsRef<'tcx>,
    discr: Exp,
    brch: Box<[(VariantIdx, BasicBlock)]>,
    default: Option<BasicBlock>,
) -> Box<[Defn]> {
    assert!(adt.is_enum());

    let LoweringState { ctx, names, block_idents, .. } = *lower;
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
                    let id: Ident = Ident::fresh_local(format!("x{}", ix.as_usize()));
                    (
                        Param::Term(
                            id,
                            translate_ty(ctx, names, DUMMY_SP, field.ty(ctx.tcx, subst)),
                        ),
                        Exp::var(id),
                    )
                })
                .unzip();

            let cons = names.constructor(var.def_id, subst);
            let body = Exp::var(cons).app(ids);
            let body = Expr::assert(discr.clone().eq(body), mk_goto(block_idents, tgt).black_box());
            let name = Ident::fresh_local(format!("br{}", ix.as_usize()));

            Defn { prototype: Prototype { name, params: params.into(), attrs: vec![] }, body }
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
        Defn::simple(Ident::fresh_local(format!("br{ix}")), filter)
    })
}

impl<'tcx> Block<'tcx> {
    fn into_why<N: Namer<'tcx>>(
        self,
        lower: &mut LoweringState<'_, 'tcx, N>,
        id: BasicBlock,
    ) -> Defn {
        let mut statements = vec![];

        let cont0 = Ident::fresh_local("s0");
        let mut cont = cont0;
        for (ix, s) in self.stmts.into_iter().enumerate() {
            let stmt = s.into_why(lower);
            let old_cont = cont;
            cont = Ident::fresh_local(format!("s{}", ix + 1));
            let body = assemble_intermediates(stmt.into_iter(), Expr::var(cont));
            statements.push(Defn::simple(old_cont, body));
        }

        let (istmts, terminator) = self.terminator.into_why(lower);
        let body = assemble_intermediates(istmts.into_iter(), terminator);
        statements.push(Defn::simple(cont, body));

        let mut body = Expr::var(cont0);
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

        Defn::simple(*lower.block_idents.get(&id).unwrap(), body)
    }
}

/// Combine `exp` and the statements `istmts` into one coma expression.
fn assemble_intermediates<I>(istmts: I, exp: Expr) -> Expr
where
    I: IntoIterator<Item = IntermediateStmt>,
    I: DoubleEndedIterator<Item = IntermediateStmt>,
{
    istmts.rfold(exp, |tail, stmt| match stmt {
        IntermediateStmt::Assign(id, exp) => tail.assign(id, exp),
        IntermediateStmt::Call(params, fun, args) => Expr::Name(fun)
            .app(args.into_iter().chain([Arg::Cont(Expr::Lambda(params, tail.boxed()))])),
        IntermediateStmt::Assume(e) => Expr::assume(e, tail),
        IntermediateStmt::Assert(e) => Expr::assert(e, tail),
        IntermediateStmt::Any(id, ty) => Expr::Defn(
            Expr::Any.boxed(),
            false,
            [Defn {
                prototype: Prototype {
                    name: Ident::fresh_local("any_"),
                    attrs: vec![],
                    params: [Param::Term(id, ty)].into(),
                },
                body: tail.black_box(),
            }]
            .into(),
        ),
    })
}

#[derive(Debug)]
pub(crate) enum IntermediateStmt {
    // [ id = E] K
    Assign(Ident, Exp),
    // E [ARGS] (id : ty -> K)
    Call(Box<[Param]>, Name, Box<[Arg]>),
    // -{ E }- K
    Assume(Exp),
    // { E } K
    Assert(Exp),

    Any(Ident, Type),
}

impl IntermediateStmt {
    fn call(id: Ident, ty: Type, f: Name, args: impl IntoIterator<Item = Arg>) -> Self {
        IntermediateStmt::Call([Param::Term(id, ty)].into(), f, args.into_iter().collect())
    }
}

impl<'tcx> Statement<'tcx> {
    fn into_why<N: Namer<'tcx>>(
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
                    Some(Exp::var(lower.names.ty_inv(rhs_ty)))
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
                            lower.ctx,
                            lower.names,
                            Some(&mut istmts),
                            rhs_local_ty,
                            Focus::new(|_| Exp::var(rhs.local)),
                            Box::new(|_, x| x),
                            &rhs.projections[..deref_index],
                            |ix| Exp::var(*ix),
                        );
                    let (_, foc, constr) = projections_to_expr(
                        lower.ctx,
                        lower.names,
                        Some(&mut istmts),
                        original_borrow_ty,
                        original_borrow.clone(),
                        original_borrow_constr,
                        &rhs.projections[deref_index..],
                        |ix| Exp::var(*ix),
                    );
                    rhs_rplace = foc.call(Some(&mut istmts));
                    rhs_constr = constr;

                    let borrow_id = borrow_generated_id(
                        lower.names,
                        original_borrow.call(Some(&mut istmts)),
                        &rhs.projections[deref_index + 1..],
                        |sym| {
                            Exp::qvar(
                                lower
                                    .names
                                    .in_pre(uty_to_prelude(lower.ctx.tcx, UintTy::Usize), "t'int"),
                            )
                            .app([Exp::var(*sym)])
                        },
                    );

                    bor_id_arg = Some(Arg::Term(borrow_id));
                } else {
                    let (_, foc, constr) = projections_to_expr(
                        lower.ctx,
                        lower.names,
                        Some(&mut istmts),
                        rhs_local_ty,
                        Focus::new(|_| Exp::var(rhs.local)),
                        Box::new(|_, x| x),
                        &rhs.projections,
                        |ix| Exp::var(*ix),
                    );
                    rhs_rplace = foc.call(Some(&mut istmts));
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
                let ret_ident = Ident::fresh_local("_ret");
                let borrow_call =
                    IntermediateStmt::call(ret_ident, lhs_ty_low, Name::Global(func), args);
                istmts.push(borrow_call);
                lower.assignment(&lhs, Exp::var(ret_ident), &mut istmts);

                let reassign = Exp::var(ret_ident).field(Name::Global(name::final_()));

                if let Some(rhs_inv_fun) = rhs_inv_fun {
                    istmts.push(IntermediateStmt::Assume(rhs_inv_fun.app([reassign.clone()])));
                }

                let new_rhs = rhs_constr(Some(&mut istmts), reassign);
                istmts.push(IntermediateStmt::Assign(rhs.local, new_rhs));
            }
            Statement::Assignment(lhs, e, _span) => {
                let rhs = e.into_why(lower, lhs.ty(lower.ctx.tcx, lower.locals), &mut istmts);
                lower.assignment(&lhs, rhs, &mut istmts);
            }
            Statement::Call(dest, fun_id, subst, args, _) => {
                let (fun_qname, args) = func_call_to_why3(lower, fun_id, subst, args, &mut istmts);
                let ty = dest.ty(lower.ctx.tcx, lower.locals);
                let ty = lower.ty(ty);
                let ret_ident = Ident::fresh_local("_ret");
                istmts.push(IntermediateStmt::call(ret_ident, ty, fun_qname, args));
                lower.assignment(&dest, Exp::var(ret_ident), &mut istmts);
            }
            Statement::Resolve { did, subst, pl } => {
                let rp = Exp::Var(lower.names.item(did, subst));
                let loc = pl.local;
                let bound = Ident::fresh_local("x");
                let pat = pattern_of_place(lower.ctx.tcx, lower.locals, pl, bound);
                let pat = lower_pat(lower.ctx, lower.names, &pat);
                let exp = if let WPattern::VarP(_) = pat {
                    rp.app([Exp::var(loc)])
                } else {
                    Exp::var(loc).match_([
                        (pat, rp.app([Exp::var(bound)])),
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
                let inv_fun = Exp::var(lower.names.ty_inv(pl.ty(lower.ctx.tcx, lower.locals)));
                let loc = pl.local;
                let bound = Ident::fresh_local("x");
                let pat = pattern_of_place(lower.ctx.tcx, lower.locals, pl, bound);
                let pat = lower_pat(lower.ctx, lower.names, &pat);
                let exp = if let WPattern::VarP(_) = pat {
                    inv_fun.app([Exp::var(loc)])
                } else {
                    Exp::var(loc).match_([
                        (pat, inv_fun.app([Exp::var(bound)])),
                        (WPattern::Wildcard, Exp::mk_true()),
                    ])
                };

                let exp = exp.with_attr(Attribute::Attr("expl:type invariant".to_string()));
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
    binder: Ident,
) -> Pattern<'tcx> {
    let mut pat = Pattern::binder(binder, pl.ty(tcx, locals));
    for (pl, el) in pl.iter_projections().rev() {
        let ty = pl.ty(tcx, locals);
        match el {
            ProjectionElem::Deref => pat = pat.deref(ty.ty),
            ProjectionElem::Field(fidx, _) => match ty.ty.kind() {
                TyKind::Adt(adt, substs) => {
                    let variant = ty.variant_index.unwrap_or(VariantIdx::ZERO);
                    let mut fields: Box<[_]> = adt.variants()[variant]
                        .fields
                        .iter()
                        .map(|f| Pattern::wildcard(f.ty(tcx, substs)))
                        .collect();
                    fields[fidx.as_usize()] = pat;
                    pat = Pattern::constructor(variant, fields, ty.ty)
                }
                TyKind::Tuple(tys) => {
                    let mut fields: Box<[_]> = tys.iter().map(Pattern::wildcard).collect();
                    fields[fidx.as_usize()] = pat;
                    pat = Pattern::tuple(fields, ty.ty)
                }
                TyKind::Closure(_, substs) => {
                    let mut fields: Box<[_]> = substs
                        .as_closure()
                        .upvar_tys()
                        .into_iter()
                        .map(Pattern::wildcard)
                        .collect();
                    fields[fidx.as_usize()] = pat;
                    pat = Pattern::constructor(VariantIdx::ZERO, fields, ty.ty)
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
) -> (Name, Box<[Arg]>) {
    // TODO: Perform this simplification earlier
    // Eliminate "rust-call" ABI
    let args: Box<[_]> = if lower.ctx.is_closure_like(id) {
        assert!(args.len() == 2, "closures should only have two arguments (env, args)");
        let [arg, Operand::Move(pl)] = *args.into_array().unwrap() else { panic!() };

        let real_sig = lower.ctx.signature_unclosure(subst.as_closure().sig(), Safety::Safe);

        once(Arg::Term(arg.into_why(lower, istmts)))
            .chain(real_sig.inputs().iter().enumerate().map(|(ix, inp)| {
                let inp = lower.ctx.instantiate_bound_regions_with_erased(inp.map_bound(|&x| x));
                let projection = pl
                    .projections
                    .iter()
                    .copied()
                    .chain([ProjectionElem::Field(ix.into(), inp)])
                    .collect();
                Arg::Term(
                    Operand::Move(Place { projections: projection, ..pl }).into_why(lower, istmts),
                )
            }))
            .collect()
    } else {
        args.into_iter().map(|a| a.into_why(lower, istmts)).map(Arg::Term).collect()
    };

    (lower.names.item(id, subst), args)
}
