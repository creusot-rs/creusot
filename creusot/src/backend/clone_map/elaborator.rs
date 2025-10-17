use crate::{
    backend::{
        self, Why3Generator,
        clone_map::{CloneNames, Dependency, Kind, Namer},
        closures::{closure_hist_inv, closure_post, closure_pre, closure_resolve},
        is_trusted_item,
        logic::{lower_logical_defn, spec_axioms},
        program,
        signature::{lower_logic_sig, lower_program_sig},
        structural_resolve::structural_resolve,
        term::{lower_pure, lower_pure_weakdep},
        ty::{
            eliminator, translate_adtdecl, translate_closure_ty, translate_tuple_ty, translate_ty,
        },
        ty_inv::{elaborate_inv, sig_add_type_invariant_spec},
    },
    contracts_items::{Intrinsic, get_builtin, is_inline, is_logic, why3_metas},
    ctx::{BodyId, HasTyCtxt as _, ItemType},
    naming::name,
    translation::{
        constant::try_const_to_term,
        pearlite::{BinOp, Pattern, QuantKind, SmallRenaming, Term, Trigger, normalize},
        specification::Condition,
        traits::TraitResolved,
    },
};
use petgraph::graphmap::DiGraphMap;
use rustc_ast::Mutability;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{
    self, AliasTyKind, Const, GenericArg, GenericArgsRef, TraitRef, Ty, TyCtxt, TyKind, TypingEnv,
};
use rustc_span::{DUMMY_SP, Span, Symbol};
use rustc_type_ir::{ClosureKind, ConstKind, EarlyBinder};
use std::{
    assert_matches::assert_matches,
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
};
use why3::{
    Exp, Ident, Name,
    coma::{Defn, Expr, Param, Prototype},
    declaration::{
        Attribute, Axiom, Decl, DeclKind, LogicDecl, Meta, MetaArg, MetaIdent, Signature, TyDecl,
        Use,
    },
};

/// Weak dependencies are allowed to form cycles in the graph, but strong ones cannot,
/// weak dependencies are used to perform an initial stratification of the dependency graph.
#[derive(PartialEq, PartialOrd, Copy, Clone, Debug)]
pub enum Strength {
    Weak,
    Strong,
}

/// The `Expander` takes a list of 'root' dependencies (items explicitly requested by user code),
/// and expands this into a complete dependency graph.
pub(super) struct Expander<'a, 'ctx, 'tcx> {
    graph: DiGraphMap<Dependency<'tcx>, Strength>,
    dep_bodies: HashMap<Dependency<'tcx>, Vec<Decl>>,
    namer: &'a mut CloneNames<'ctx, 'tcx>,
    typing_env: TypingEnv<'tcx>,
    expansion_queue: VecDeque<(Dependency<'tcx>, Strength, Dependency<'tcx>)>,
    /// Span for the item we are expanding
    root_span: Span,
}

struct ExpansionProxy<'a, 'ctx, 'tcx> {
    namer: &'a mut CloneNames<'ctx, 'tcx>,
    expansion_queue: RefCell<&'a mut VecDeque<(Dependency<'tcx>, Strength, Dependency<'tcx>)>>,
    source: Dependency<'tcx>,
}

impl<'tcx> Namer<'tcx> for ExpansionProxy<'_, '_, 'tcx> {
    fn raw_dependency(&self, dep: Dependency<'tcx>) -> &Kind {
        self.expansion_queue.borrow_mut().push_back((self.source, Strength::Strong, dep));
        self.namer.raw_dependency(dep)
    }

    fn register_constant_setter(&mut self, setter: Ident) {
        self.namer.register_constant_setter(setter);
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.namer.tcx()
    }

    fn source_id(&self) -> DefId {
        self.namer.source_id()
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        self.namer.typing_env()
    }

    fn span(&self, span: Span) -> Option<Attribute> {
        self.namer.span(span)
    }

    fn bitwise_mode(&self) -> bool {
        self.namer.bitwise_mode()
    }
}

fn expand_program<'tcx>(
    elab: &mut Expander<'_, '_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::Item(def_id, subst);
    let typing_env = elab.typing_env;
    let names = elab.namer(dep);

    let name = names.dependency(dep).ident();

    let mut pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx, typing_env);

    if ctx.def_kind(def_id) == DefKind::Closure {
        // Inline the body of closures
        let mut decls = vec![Decl::Coma(program::to_why(ctx, &names, name, def_id.expect_local()))];
        if !pre_sig.contract.has_user_contract {
            decls.extend(["'pre", "'post'return"].map(|s| {
                Decl::Meta(Meta {
                    name: MetaIdent("rewrite_def".into()),
                    args: Box::new([
                        MetaArg::Keyword("predicate".into()),
                        MetaArg::Name(Name::Local(name, Some(why3::Symbol::intern(s)))),
                    ]),
                })
            }))
        }
        return decls;
    }

    if matches!(ctx.intrinsic(def_id), Intrinsic::GhostDeref | Intrinsic::GhostDerefMut) {
        // If `Ghost::deref`` or `Ghost::deref_mut` are called direclty, then
        // the validation pass has checked that the call is in the right context.
        // Hence we can remove the precondition `#[requires(false)]` which was protecting
        // against indirect calls (via generics).
        pre_sig.contract.requires.clear();
    }

    if let TraitResolved::UnknownFound = TraitResolved::resolve_item(ctx.tcx, typing_env, def_id, subst)
                // These conditions are important to make sure the Fn trait familly is implemented
                && ctx.fn_sig(def_id).skip_binder().is_fn_trait_compatible()
                && ctx.codegen_fn_attrs(def_id).target_features.is_empty()
    {
        let fn_name = ctx.item_name(def_id);

        let args =
            Term::tuple(ctx.tcx, pre_sig.inputs.iter().map(|&(nm, _, ty)| Term::var(nm, ty)));
        let fndef_ty = Ty::new_fn_def(ctx.tcx, def_id, subst);

        let pre_post_subst = ctx.mk_args(&[args.ty, fndef_ty].map(GenericArg::from));

        let pre_did = Intrinsic::Precondition.get(ctx);
        let pre_args = [Term::unit(ctx.tcx).coerce(fndef_ty), args.clone()];
        let pre = Term::call(ctx.tcx, typing_env, pre_did, pre_post_subst, pre_args);
        let expl_pre = format!("expl:{} requires", fn_name);
        pre_sig.contract.requires = vec![Condition { term: pre, expl: expl_pre }];

        let post_did = Intrinsic::PostconditionOnce.get(ctx);
        let post_args =
            [Term::unit(ctx.tcx).coerce(fndef_ty), args, Term::var(name::result(), pre_sig.output)];
        let post = Term::call(ctx.tcx, typing_env, post_did, pre_post_subst, post_args);
        let expl_post = format!("expl:{} ensures", fn_name);
        pre_sig.contract.ensures = vec![Condition { term: post, expl: expl_post }]
    } else {
        sig_add_type_invariant_spec(ctx, typing_env, names.source_id(), &mut pre_sig, def_id)
    }

    let sig = lower_program_sig(ctx, &names, name, pre_sig, def_id, name::return_());
    vec![program::val(sig.prototype, sig.contract, sig.return_ty)]
}

/// Expand a logical item
fn expand_logic<'tcx>(
    elab: &mut Expander<'_, '_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::Item(def_id, subst);

    if Intrinsic::Inv.is(ctx, def_id) {
        elab.expansion_queue.push_back((
            dep,
            Strength::Weak,
            Dependency::TyInvAxiom(subst.type_at(0)),
        ));
    }

    if get_builtin(ctx.tcx, def_id).is_some() {
        match elab.namer.dependency(dep) {
            Kind::Named(_) => return vec![],
            Kind::UsedBuiltin(qname) => {
                if qname.module.is_empty() {
                    return vec![];
                } else {
                    return vec![Decl::UseDecls(Box::new([Use {
                        name: qname.module.clone(),
                        export: false,
                    }]))];
                }
            }
            Kind::Unnamed => unreachable!(),
        }
    }

    let typing_env = elab.typing_env;
    let pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx, typing_env);

    let bound: Box<[Ident]> = pre_sig.inputs.iter().map(|(ident, _, _)| ident.0).collect();
    let trait_resol = TraitResolved::resolve_item(ctx.tcx, typing_env, def_id, subst);
    assert_matches!(
        trait_resol,
        TraitResolved::NotATraitItem
            | TraitResolved::Instance { .. } // The default impl is known to be the final instance
            | TraitResolved::UnknownFound // Unresolved trait method
    );
    // The other case are impossible, because that would mean we are not guaranteed to have an instance

    let opaque = matches!(trait_resol, TraitResolved::UnknownFound)
        || !ctx.is_transparent_from(def_id, elab.namer.source_id());

    let names = elab.namer(dep);
    let name = names.dependency(dep).ident();
    let sig = lower_logic_sig(ctx, &names, name, pre_sig, def_id);
    let kind = match sig.why_sig.retty {
        None => DeclKind::Predicate,
        Some(_) if sig.why_sig.args.is_empty() => DeclKind::Constant,
        _ => DeclKind::Function,
    };
    let mut decls = if !opaque && let Some(term) = term(ctx, &names, &bound, def_id, subst) {
        lower_logical_defn(ctx, &names, sig, kind, term, is_inline(ctx.tcx, def_id))
    } else {
        let mut decls = val(sig.why_sig, kind);

        if matches!(
            ctx.intrinsic(def_id),
            Intrinsic::Precondition
                | Intrinsic::Postcondition
                | Intrinsic::PostconditionMut
                | Intrinsic::PostconditionOnce
        ) && let &TyKind::FnDef(did_f, subst_f) = subst.type_at(1).kind()
        {
            // No definite instance if found for this method, so `term` has returned `None`
            // However, we still emit an axiom telling that the specification should be a refinement.
            let args_id = Ident::fresh_local("args").into();
            let args_tup = Term::var(args_id, subst.type_at(0));

            let res_id = Ident::fresh_local("res").into();
            let res_ty = ctx.instantiate_bound_regions_with_erased(
                ctx.fn_sig(did_f).instantiate(ctx.tcx, subst_f).output(),
            );
            let res = Term::var(res_id, res_ty);

            let mut args = vec![Term::unit(ctx.tcx).coerce(subst.type_at(1)), args_tup.clone()];
            match ctx.intrinsic(def_id) {
                Intrinsic::Precondition => (),
                Intrinsic::Postcondition | Intrinsic::PostconditionOnce => args.push(res.clone()),
                Intrinsic::PostconditionMut => {
                    args.extend([Term::unit(ctx.tcx).coerce(subst.type_at(1)), res.clone()])
                }
                _ => unreachable!(),
            };

            let call = Term::call(ctx.tcx, typing_env, def_id, subst, args);
            let trig = Box::new([Trigger(Box::new([call.clone()]))]);

            if Intrinsic::Precondition.is(ctx, def_id) {
                if let Some(pre) = pre_fndef(ctx, &names, did_f, subst_f, args_tup) {
                    let axiom = pre.implies(call).forall_trig((args_id, subst.type_at(0)), trig);
                    decls.push(Decl::Axiom(Axiom {
                        name: Ident::fresh(ctx.crate_name(), "precondition_fndef"),
                        rewrite: false,
                        axiom: lower_pure(ctx, &names, &axiom),
                    }))
                }
            } else if let Some(post) = post_fndef(ctx, &names, did_f, subst_f, args_tup, res) {
                let axiom = call.implies(post).quant(
                    QuantKind::Forall,
                    Box::new([(args_id, subst.type_at(0)), (res_id, res_ty)]),
                    trig,
                );
                decls.push(Decl::Axiom(Axiom {
                    name: Ident::fresh(ctx.crate_name(), "postcondition_fndef"),
                    rewrite: false,
                    axiom: lower_pure(ctx, &names, &axiom),
                }))
            }
        }

        decls
    };
    match ctx.intrinsic(def_id) {
        Intrinsic::SizeOfLogic => {
            decls.extend(axiom_nonzero_size_of(ctx, typing_env, name, subst.type_at(0)))
        }
        _ => {}
    }
    decls.extend(why3_metas(ctx.tcx, def_id, name).map(|m| Decl::Meta(m)));
    decls
}

/// Generate an axiom `is_sized_logic > 0` if that can be guaranteed and the type does not already
/// have a known constant size.
fn axiom_nonzero_size_of<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    name: Ident,
    ty: Ty<'tcx>,
) -> Option<Decl> {
    let size_unknown =
        ctx.tcx.layout_of(ty::PseudoCanonicalInput { typing_env, value: ty }).is_err();
    if size_unknown && ctx.is_nonzero_sized(ty) {
        Some(Decl::Axiom(Axiom {
            name: Ident::fresh_local(format!("nonzero_{}", name.name().to_string())),
            rewrite: false,
            axiom: Exp::BinaryOp(why3::exp::BinOp::Gt, Exp::var(name).boxed(), Exp::int(0).boxed()),
        }))
    } else {
        None
    }
}

/// Constants require some special handling because they can be defined with arbitrary Rust expressions
/// which we only know how to translate to Coma, but we also want to be able to use them in logic contexts (Pearlite).
///
/// For simple definitions (variables, literals, constructors), we call `try_const_to_term` to translate them
/// to a pure Why3 expression as the body of a `constant` declaration.
///
/// Otherwise, a constant is translated to a `constant` declaration with no body and a Coma function which we call its "constant setter".
/// The constant setter contains the Coma translation of the constant definition. It constructs the value of the constant,
/// and performs an *assume* statement that the constructed value is equal to the previously declared constant.
/// In the final declaration of each module, we wrap the body with calls to all constant setters.
fn expand_constant<'tcx>(
    elab: &mut Expander<'_, '_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::Item(def_id, subst);

    let typing_env = elab.typing_env;
    let trait_resol = TraitResolved::resolve_item(ctx.tcx, typing_env, def_id, subst);
    assert_matches!(
        trait_resol,
        TraitResolved::NotATraitItem
            | TraitResolved::Instance { .. } // The default impl is known to be the final instance
            | TraitResolved::UnknownFound // Unresolved trait method
    );
    let opaque = matches!(trait_resol, TraitResolved::UnknownFound)
        || ctx.def_kind(def_id) == DefKind::ConstParam
        || !ctx.is_transparent_from(def_id, elab.namer.source_id());

    let mut names = elab.namer(dep);
    let name = names.dependency(dep).ident();
    let mut pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx, typing_env);
    sig_add_type_invariant_spec(ctx, typing_env, names.source_id(), &mut pre_sig, def_id);
    let sig = lower_logic_sig(ctx, &names, name, pre_sig, def_id);

    if opaque {
        val(sig.why_sig, DeclKind::Constant)
    } else if let Some(term) = try_const_to_term(def_id, subst, ctx, typing_env) {
        lower_logical_defn(ctx, &names, sig, DeclKind::Constant, term, is_inline(ctx.tcx, def_id))
    } else {
        let mut decls = val(sig.why_sig, DeclKind::Constant);
        decls.push(const_setter(ctx, &mut names, name, def_id, subst));
        decls
    }
}

/// Generate a constant setter. The constant `(def_id, subst)` is expected to have a body.
fn const_setter<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &mut impl Namer<'tcx>,
    name: Ident,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Decl {
    let span = ctx.def_span(def_id);
    let body_id = BodyId::from_def_id(def_id);
    let outer_return = Ident::fresh_local("ret");
    let inner_return = Ident::fresh_local("const_ret");
    let value_name = Ident::fresh_local("_const");
    let setter = Ident::fresh_local(format!(
        "set_{}",
        crate::naming::translate_name(ctx.ctx.item_name(def_id).as_str())
    ));
    let body = program::why_body(
        ctx,
        names,
        body_id,
        Some(subst),
        &[],
        inner_return,
        &mut Default::default(),
    );
    let ty = translate_ty(ctx, names, span, ctx.sig(def_id).output);
    let inner_def = Defn {
        prototype: Prototype::new(inner_return, [Param::Term(value_name, ty)]),
        body: Expr::Assume(
            Exp::var(name).eq(Exp::var(value_name)).boxed(),
            Expr::var(outer_return).app([]).boxed(),
        ),
    };
    let prototype = Prototype::new(setter, [Param::Cont(outer_return, [].into(), [].into())]);
    let body = Expr::Defn(body.boxed(), false, [inner_def].into());
    let defn = Defn { prototype, body };
    names.register_constant_setter(setter);
    Decl::Coma(defn)
}

// TODO Deprecate and fold into LogicElab
fn expand_ty_inv_axiom<'tcx>(
    elab: &mut Expander<'_, '_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let root_span = elab.root_span;
    let names = elab.namer(Dependency::TyInvAxiom(ty));
    let Some((term, rewrite)) = elaborate_inv(ctx, &names, ty, root_span) else {
        return vec![];
    };
    let axiom = lower_pure_weakdep(ctx, &names, &term);
    let axiom =
        Axiom { name: names.dependency(Dependency::TyInvAxiom(ty)).ident(), rewrite, axiom };
    vec![Decl::Axiom(axiom)]
}

fn expand_type<'tcx>(
    elab: &mut Expander<'_, '_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::Type(ty);
    let typing_env = elab.typing_env;
    let names = elab.namer(dep);
    match ty.kind() {
        TyKind::Param(_) => vec![Decl::TyDecl(TyDecl::Opaque {
            ty_name: names.ty(ty).to_ident(),
            ty_params: Box::new([]),
        })],
        TyKind::Alias(AliasTyKind::Opaque | AliasTyKind::Projection, _) => {
            let (def_id, subst) = dep.did().unwrap();
            vec![Decl::TyDecl(TyDecl::Opaque {
                ty_name: names.def_ty(def_id, subst).to_ident(),
                ty_params: Box::new([]),
            })]
        }
        TyKind::Closure(did, subst) => translate_closure_ty(ctx, &names, *did, subst),
        TyKind::Adt(_, _) => translate_adtdecl(ctx, &names, ty, typing_env),
        TyKind::Tuple(_) => translate_tuple_ty(ctx, &names, ty),
        TyKind::Dynamic(traits, _) => {
            if is_logically_dyn_compatible(ctx.tcx(), traits.iter()) {
                vec![Decl::TyDecl(TyDecl::Opaque {
                    ty_name: names.ty(ty).to_ident(),
                    ty_params: Box::new([]),
                })]
            } else {
                ctx.crash_and_error(DUMMY_SP, format!("forbidden dyn type: {} (dyn support is currently minimal, please open an issue to improve this feature)", ty))
            }
        }
        _ => unreachable!("unsupported type: {ty}"),
    }
}

/// Trait bound for which `dyn` is supported by Creusot
/// (Rust already has a notion of "dyn-compatibility", this is a refinement of that
/// which we thus call "logical dyn-compatibility".)
fn is_logically_dyn_compatible<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    traits: impl IntoIterator<Item = ty::Binder<'tcx, ty::ExistentialPredicate<'tcx>>>,
) -> bool {
    traits.into_iter().any(|b| match b.skip_binder() {
        ty::ExistentialPredicate::Trait(tr) => is_logically_dyn_compatible_trait(tcx, tr.def_id),
        _ => false,
    })
}

/// Base trait for which `dyn` is supported by Creusot
fn is_logically_dyn_compatible_trait<'tcx>(tcx: ty::TyCtxt<'tcx>, tr: DefId) -> bool {
    // TODO: support more traits
    let Some(path) = def_path(tcx, tr) else { return false };
    [["core", "fmt", "Debug"], ["core", "fmt", "Write"]].iter().any(|p| equal_path(&*path, &*p))
}

fn equal_path(a: &[Symbol], b: &[&str]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| a.as_str() == *b)
}

fn def_path(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Vec<Symbol>> {
    let mut path = vec![tcx.crate_name(def_id.krate)];
    for seg in tcx.def_path(def_id).data {
        match seg.data {
            rustc_hir::definitions::DefPathData::TypeNs(name) => path.push(name),
            _ => return None,
        }
    }
    Some(path)
}

fn expand_dyn_cast<'tcx>(
    elab: &mut Expander<'_, '_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::DynCast(source, target);
    let names = elab.namer(dep);
    let sig = Signature {
        name: names.dependency(dep).ident(),
        trigger: None,
        attrs: vec![],
        retty: Some(translate_ty(ctx, &names, DUMMY_SP, target)),
        args: [(Ident::fresh_local("x"), translate_ty(ctx, &names, DUMMY_SP, source))].into(),
        contract: Default::default(),
    };
    vec![Decl::LogicDecl(LogicDecl { kind: Some(DeclKind::Function), sig })]
}

impl<'a, 'ctx, 'tcx> Expander<'a, 'ctx, 'tcx> {
    /// # Parameters
    ///
    /// `span`: span of the item being expanded
    pub(crate) fn new(
        namer: &'a mut CloneNames<'ctx, 'tcx>,
        typing_env: TypingEnv<'tcx>,
        initial: impl Iterator<Item = Dependency<'tcx>>,
        span: Span,
    ) -> Self {
        let source_item = namer.source_item();
        Self {
            graph: Default::default(),
            namer,
            typing_env,
            expansion_queue: initial.map(|b| (source_item, Strength::Strong, b)).collect(),
            dep_bodies: Default::default(),
            root_span: span,
        }
    }

    fn namer(&mut self, source: Dependency<'tcx>) -> ExpansionProxy<'_, 'ctx, 'tcx> {
        ExpansionProxy {
            namer: self.namer,
            expansion_queue: RefCell::new(&mut self.expansion_queue),
            source,
        }
    }

    /// Expand the graph with new entries
    pub fn update_graph(
        mut self,
        ctx: &Why3Generator<'tcx>,
    ) -> (DiGraphMap<Dependency<'tcx>, Strength>, HashMap<Dependency<'tcx>, Vec<Decl>>) {
        let mut visited = HashSet::new();
        while let Some((s, strength, t)) = self.expansion_queue.pop_front() {
            if let Some(old) = self.graph.add_edge(s, t, strength)
                && old > strength
            {
                self.graph.add_edge(s, t, old);
            }

            if !visited.insert(t) {
                continue;
            }
            self.expand(ctx, t);
        }

        (self.graph, self.dep_bodies)
    }

    fn expand(&mut self, ctx: &Why3Generator<'tcx>, dep: Dependency<'tcx>) {
        expand_laws(self, ctx, dep);

        let decls = match dep {
            Dependency::Type(ty) => expand_type(self, ctx, ty),
            Dependency::Item(def_id, subst) => match ctx.item_type(def_id) {
                ItemType::Logic { .. } => expand_logic(self, ctx, def_id, subst),
                ItemType::Constant => expand_constant(self, ctx, def_id, subst),
                ItemType::Field | ItemType::Variant => {
                    self.namer(dep).def_ty(ctx.parent(def_id), subst);
                    vec![]
                }
                ItemType::Program | ItemType::Closure => expand_program(self, ctx, def_id, subst),
                item_type => {
                    let path = ctx.def_path_str(def_id);
                    let self_path = ctx.def_path_str(self.namer.source_id());
                    ctx.crash_and_error(self.root_span, format!("expanding {path:?} failed because of unexpected kind {item_type:?} while translating {self_path:?}"))
                }
            },
            Dependency::TyInvAxiom(ty) => expand_ty_inv_axiom(self, ctx, ty),
            Dependency::ClosureAccessor(_, _, _) | Dependency::TupleField(_, _) => vec![],
            Dependency::PreMod(b) => {
                vec![Decl::UseDecls(Box::new([Use {
                    name: self.namer.prelude_module_name(b),
                    export: false,
                }]))]
            }
            Dependency::Eliminator(def_id, subst) => {
                vec![eliminator(ctx, &self.namer(dep), def_id, subst)]
            }
            Dependency::DynCast(source, target) => expand_dyn_cast(self, ctx, source, target),
        };

        self.dep_bodies.insert(dep, decls);
    }
}

fn traitref_of_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<TraitRef<'tcx>> {
    let ai = tcx.opt_associated_item(did)?;
    let cont = ai.container_id(tcx);
    let subst = tcx.mk_args_from_iter(subst.iter().take(tcx.generics_of(cont).count()));

    if tcx.def_kind(cont) == DefKind::Trait {
        return Some(TraitRef::new(tcx, cont, subst));
    }

    let trait_ref = tcx.impl_trait_ref(cont)?.instantiate(tcx, subst);
    Some(tcx.normalize_erasing_regions(typing_env, trait_ref))
}

fn expand_laws<'tcx>(
    elab: &mut Expander<'_, '_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    dep: Dependency<'tcx>,
) {
    let (self_did, self_subst) = (elab.namer.source_id(), elab.namer.source_subst());
    let Some((item_did, item_subst)) = dep.did() else {
        return;
    };

    let Some(item_ai) = ctx.opt_associated_item(item_did) else { return };
    let item_container = item_ai.container_id(ctx.tcx);

    // Dont clone laws into the trait / impl which defines them.
    if let Some(tr_item) = traitref_of_item(ctx.tcx, elab.typing_env, item_did, item_subst)
        && let Some(tr_self) = traitref_of_item(ctx.tcx, elab.typing_env, self_did, self_subst)
        && tr_item == tr_self
    {
        return;
    }

    // TODO: Push out of graph expansion
    // If the function we are cloning into is `#[trusted]` there is no need for laws.
    // Similarily, if it has no body, there will be no proofs.
    if is_trusted_item(ctx.tcx, self_did) || !ctx.has_body(self_did) {
        return;
    }

    for law in ctx.laws(item_container) {
        let law_dep = elab.namer(dep).resolve_dependency(Dependency::Item(*law, item_subst));
        // We add a weak dep from `dep` to make sure it appears close to the triggering item
        elab.expansion_queue.push_back((dep, Strength::Weak, law_dep));
    }
}

fn val(mut sig: Signature, kind: DeclKind) -> Vec<Decl> {
    if let None = sig.retty
        && let DeclKind::Constant = kind
    {
        sig.retty = Some(backend::ty::bool());
    }
    let mut d = spec_axioms(&sig).collect::<Vec<_>>();
    sig.contract = Default::default();
    d.insert(0, Decl::LogicDecl(LogicDecl { kind: Some(kind), sig }));
    d
}

/// Generate body of `resolve`
fn resolve_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let def_id = Intrinsic::Resolve.get(ctx);
    let sig = ctx.sig(def_id).clone();
    let mut pre_sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
    pre_sig = pre_sig.normalize(ctx, typing_env);

    let arg = Term::var(pre_sig.inputs[0].0, pre_sig.inputs[0].2);

    if let &TyKind::Closure(def_id, subst) = subst[0].as_type().unwrap().kind() {
        Some(closure_resolve(ctx, def_id, subst, bound))
    } else {
        let trait_meth_id = Intrinsic::ResolveMethod.get(ctx);
        match TraitResolved::resolve_item(ctx.tcx, typing_env, trait_meth_id, subst) {
            TraitResolved::NotATraitItem => unreachable!(),
            TraitResolved::Instance { def: (meth_did, meth_substs), .. } => {
                // We know the instance => body points to it
                Some(Term::call(ctx.tcx, typing_env, meth_did, meth_substs, [arg]))
            }
            TraitResolved::UnknownFound | TraitResolved::UnknownNotFound => {
                // We don't know the instance => body is opaque
                None
            }
            TraitResolved::NoInstance => {
                // We know there is no instance => body is true
                Some(Term::true_(ctx.tcx))
            }
        }
    }
}

/// Generate body of `postcondition_once`
fn postcondition_once_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let typing_env = names.typing_env();
    let &[self_, args, result] = bound else {
        panic!("postcondition_once must have 3 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(Intrinsic::PostconditionOnce.get(ctx)).inputs[2].2),
    );
    let res = Term::var(result, ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => {
            let mut post =
                closure_post(ctx, ClosureKind::FnOnce, did.expect_local(), self_, args, None);
            post.subst(&SmallRenaming([(name::result(), result)]));
            Some(post)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if Intrinsic::FnGhostWrapper.is(ctx, def.did()) => {
            let mut subst_postcond = subst.to_vec();
            let closure_ty = def.all_fields().next().unwrap().ty(ctx.tcx, subst_inner);
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::Postcondition.get(ctx);
            let post_args = [self_.proj(0usize.into(), closure_ty), args, res];
            Some(Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args))
        }
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::PostconditionMut.get(ctx);
            let post_args = [self_.clone().cur(), args, self_.fin(), res];
            Some(Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args))
        }
        TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::Postcondition.get(ctx);
            let post_args = [self_.coerce(*cl), args, res];
            Some(Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args))
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = bsubst[0];
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::PostconditionOnce.get(ctx);
            let post_args = [self_.coerce(bsubst.type_at(0)), args, res];
            Some(Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            post_fndef(ctx, names, did, subst, args, res)
        }
        _ => None,
    }
}

/// Generate body of `postcondition_mut`
fn postcondition_mut_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let typing_env = names.typing_env();
    let &[self_, args, result_state, result] = bound else {
        panic!("postcondition_mut must have 4 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));
    let result_state = Term::var(result_state, ty_self);
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(Intrinsic::PostconditionMut.get(ctx)).inputs[3].2),
    );
    let res = Term::var(result, ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => {
            let mut post = closure_post(
                ctx,
                ClosureKind::FnMut,
                did.expect_local(),
                self_,
                args,
                Some(result_state),
            );
            post.subst(&SmallRenaming([(name::result(), result)]));
            Some(post)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if Intrinsic::FnGhostWrapper.is(ctx, def.did()) => {
            let mut subst_postcond = subst.to_vec();
            let closure_ty = def.all_fields().next().unwrap().ty(ctx.tcx, subst_inner);
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::Postcondition.get(ctx);
            let post_args = [self_.clone().proj(0usize.into(), closure_ty), args, res];
            Some(
                Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args)
                    .conj(self_.eq(ctx.tcx, result_state)),
            )
        }
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::PostconditionMut.get(ctx);
            let post_args = [self_.clone().cur(), args, result_state.clone().cur(), res];
            Some(
                Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args)
                    .conj(self_.fin().eq(ctx.tcx, result_state.fin())),
            )
        }
        TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_args = [self_.clone().coerce(*cl), args, res];
            let post_fn = Intrinsic::Postcondition.get(ctx);
            Some(
                Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args)
                    .conj(self_.eq(ctx.tcx, result_state)),
            )
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = bsubst[0];
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::PostconditionMut.get(ctx);
            let closure_ty = bsubst.type_at(0);
            let post_args = [self_.coerce(closure_ty), args, result_state.coerce(closure_ty), res];
            Some(Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            post_fndef(ctx, names, did, subst, args, res)
        }
        _ => None,
    }
}

/// Generate body of `postcondition`
fn postcondition_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let typing_env = names.typing_env();
    let &[self_, args, result] = bound else {
        panic!("postcondition must have 3 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(Intrinsic::Postcondition.get(ctx)).inputs[2].2),
    );
    let res = Term::var(result, ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => {
            let mut post =
                closure_post(ctx, ClosureKind::Fn, did.expect_local(), self_, args, None);
            post.subst(&SmallRenaming([(name::result(), result)]));
            Some(post)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if Intrinsic::FnGhostWrapper.is(ctx, def.did()) => {
            let closure_ty = def.all_fields().next().unwrap().ty(ctx.tcx, subst_inner);
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::Postcondition.get(ctx);
            let post_args = [self_.proj(0usize.into(), closure_ty), args, res];
            Some(Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args))
        }
        &TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(cl);
            let subst_postcond = ctx.tcx.mk_args(&subst_postcond);
            let post_fn = Intrinsic::Postcondition.get(ctx);
            let post_args = [self_.clone().coerce(cl), args, res];
            Some(Term::call(ctx.tcx, typing_env, post_fn, subst_postcond, post_args))
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = bsubst[0];
            let subst_postcond = ctx.tcx.mk_args(&subst_postcond);
            let post_args = [self_.coerce(bsubst.type_at(0)), args, res];
            Some(Term::call(
                ctx.tcx,
                typing_env,
                Intrinsic::Postcondition.get(ctx),
                subst_postcond,
                post_args,
            ))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            post_fndef(ctx, names, did, subst, args, res)
        }
        _ => None,
    }
}

fn post_fndef<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Term<'tcx>,
    res: Term<'tcx>,
) -> Option<Term<'tcx>> {
    if is_logic(ctx.tcx, did) {
        return None;
    }

    let mut sig = EarlyBinder::bind(ctx.sig(did).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx, names.typing_env());
    sig_add_type_invariant_spec(ctx, names.typing_env(), names.source_id(), &mut sig, did);
    let mut post = sig.contract.ensures_conj(ctx.tcx);
    post.subst(&HashMap::from([(name::result(), res.kind)]));
    let pattern = Pattern::tuple(
        sig.inputs.iter().map(|&(nm, span, ty)| Pattern::binder_sp(nm, span, ty)),
        args.ty,
    );
    Some(Term::let_(pattern, args, post).span(ctx.def_span(did)))
}

/// Generate body of `precondition_once` for `FnOnce` closures.
fn precondition_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let typing_env = names.typing_env();
    let &[self_, args] = bound else {
        panic!("precondition_once must have 2 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));

    match ty_self.kind() {
        TyKind::Closure(did, _) => Some(closure_pre(ctx, did.expect_local(), self_, args)),
        &TyKind::Ref(_, cl, m) => {
            let mut subst_pre = subst.to_vec();
            subst_pre[1] = GenericArg::from(cl);
            let subst_pre = ctx.mk_args(&subst_pre);
            let self_ = if m == Mutability::Mut { self_.clone().cur() } else { self_.coerce(cl) };
            let pre_fn = Intrinsic::Precondition.get(ctx);
            let pre_args = [self_, args];
            Some(Term::call(ctx.tcx, typing_env, pre_fn, subst_pre, pre_args))
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_pre = subst.to_vec();
            subst_pre[1] = bsubst[0];
            let subst_pre = ctx.mk_args(&subst_pre);
            let pre_fn = Intrinsic::Precondition.get(ctx);
            let pre_args = [self_.coerce(bsubst.type_at(0)), args];
            Some(Term::call(ctx.tcx, typing_env, pre_fn, subst_pre, pre_args))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            pre_fndef(ctx, names, did, subst, args)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if Intrinsic::FnGhostWrapper.is(ctx, def.did()) => {
            let mut subst_postcond = subst.to_vec();
            let closure_ty = def.all_fields().next().unwrap().ty(ctx.tcx, subst_inner);
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let pre_fn = Intrinsic::Precondition.get(ctx);
            let pre_args = [self_.proj(0usize.into(), closure_ty), args];
            Some(Term::call(ctx.tcx, typing_env, pre_fn, subst_postcond, pre_args))
        }
        _ => None,
    }
}

fn pre_fndef<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Term<'tcx>,
) -> Option<Term<'tcx>> {
    if is_logic(ctx.tcx, did) {
        // This is especially important for Snapshot::deref, which should keep have a false
        // precondition if called in a program via a generic.
        return None;
    }
    let mut sig = EarlyBinder::bind(ctx.sig(did).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx, names.typing_env());
    sig_add_type_invariant_spec(ctx, names.typing_env(), names.source_id(), &mut sig, did);
    let pre = sig.contract.requires_conj(ctx.tcx);
    let pattern = Pattern::tuple(
        sig.inputs.iter().map(|&(nm, span, ty)| Pattern::binder_sp(nm, span, ty)),
        args.ty,
    );
    Some(Term::let_(pattern, args, pre).span(ctx.def_span(did)))
}

fn fn_mut_hist_inv_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let &[self_, future] = bound else {
        panic!("hist_inv must have 2 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);

    match ty_self.kind() {
        TyKind::Closure(did, _) => Some(closure_hist_inv(
            ctx,
            did.expect_local(),
            Term::var(self_, ty_self),
            Term::var(future, ty_self),
        )),
        TyKind::Ref(_, _, Mutability::Not) => {
            Some(Term::var(self_, ty_self).eq(ctx.tcx, Term::var(future, ty_self)))
        }
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let hist_inv = Intrinsic::HistInv.get(ctx);
            let mut subst_hist_inv = subst.to_vec();
            subst_hist_inv[1] = GenericArg::from(*cl);
            let subst_hist_inv = ctx.mk_args(&subst_hist_inv);
            let hist_inv_args = [Term::var(self_, ty_self).cur(), Term::var(future, ty_self).cur()];
            Some(Term::call(ctx.tcx, typing_env, hist_inv, subst_hist_inv, hist_inv_args).conj(
                Term::var(self_, ty_self).fin().eq(ctx.tcx, Term::var(future, ty_self).fin()),
            ))
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let hist_inv = Intrinsic::HistInv.get(ctx);
            let mut subst_hist_inv = subst.to_vec();
            subst_hist_inv[1] = bsubst[0];
            let subst_hist_inv = ctx.mk_args(&subst_hist_inv);
            let closure_ty = bsubst.type_at(0);
            let hist_inv_args = [
                Term::var(self_, ty_self).coerce(closure_ty),
                Term::var(future, ty_self).coerce(closure_ty),
            ];
            Some(Term::call(ctx.tcx, typing_env, hist_inv, subst_hist_inv, hist_inv_args))
        }
        TyKind::FnDef(_, _) => Some(Term::true_(ctx.tcx)),
        _ => None,
    }
}

/// Special definition for `::creusot_contracts::std::mem::size_of_logic`.
///
/// The specification of sizes is documented at [`size_of`].
/// Note: at this point we are guaranteed to have a `Sized` type.
///
/// [`size_of`]: https://doc.rust-lang.org/std/mem/fn.size_of.html
fn size_of_logic_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    size_of_logic_id: DefId,
    ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    use rustc_type_ir::TyKind::*;
    if let Ok(layout) = ctx.tcx.layout_of(ty::PseudoCanonicalInput { typing_env, value: ty }) {
        // Rustc has computed a concrete size for this type. Just use it.
        // This handles at least primitive types, references, pointers, and ZSTs.
        return Some(Term::int(ctx.int_ty(), layout.size.bytes() as i128));
    }
    match ty.kind() {
        Array(t, n) => size_of_array(ctx, typing_env, size_of_logic_id, *t, n),
        _ => None, // TODO: Adts that are repr(C)
    }
}

fn size_of_array<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    size_of_logic_id: DefId,
    ty: Ty<'tcx>,
    n: &Const<'tcx>,
) -> Option<Term<'tcx>> {
    let n = match n.kind() {
        ConstKind::Value(v) => match *v.valtree {
            ty::ValTreeKind::Leaf(scalar) => scalar.to_target_usize(ctx.tcx) as i128,
            ty::ValTreeKind::Branch(_) => return None,
        },
        // TODO: ConstKind::Param
        _ => return None,
    };
    let subst = ctx.mk_args(&[ty.into()]);
    let item_size = Term::call(ctx.tcx, typing_env, size_of_logic_id, subst, []);
    Some(item_size.bin_op(ctx.int_ty(), BinOp::Mul, Term::int(ctx.int_ty(), n)))
}

fn size_of_val_logic_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    subst: GenericArgsRef<'tcx>,
    args: &[Ident],
) -> Option<Term<'tcx>> {
    let param = subst.type_at(0);
    if param.is_sized(ctx.tcx, names.typing_env()) {
        let size_of_val_logic_sized = Intrinsic::SizeOfValLogicSized.get(ctx);
        return term(ctx, names, args, size_of_val_logic_sized, subst);
    }
    match param.kind() {
        TyKind::Slice(ty) => {
            let size_of_val_logic_slice = Intrinsic::SizeOfValLogicSlice.get(ctx);
            return term(ctx, names, args, size_of_val_logic_slice, ctx.mk_args(&[(*ty).into()]));
        }
        TyKind::Str => {
            let size_of_val_logic_str = Intrinsic::SizeOfValLogicStr.get(ctx);
            return term(ctx, names, args, size_of_val_logic_str, ctx.mk_args(&[]));
        }
        _ => None,
    }
}

fn align_of_logic_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    align_of_logic_id: DefId,
    ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    use rustc_type_ir::TyKind::*;
    if let Ok(layout) = ctx.tcx.layout_of(ty::PseudoCanonicalInput { typing_env, value: ty }) {
        // Rustc has computed a concrete size for this type. Just use it.
        // This handles at least primitive types, references, pointers, and ZSTs.
        return Some(Term::int(ctx.int_ty(), layout.align.bytes() as i128));
    }
    match ty.kind() {
        Array(t, _) => {
            let subst = ctx.mk_args(&[(*t).into()]);
            let align_of_item = Term::call(ctx.tcx, typing_env, align_of_logic_id, subst, []);
            Some(align_of_item)
        }
        _ => None, // TODO: Adts that are repr(C)
    }
}

fn is_aligned_logic_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    ty: Ty<'tcx>,
    args: &[Ident],
) -> Option<Term<'tcx>> {
    use rustc_type_ir::TyKind::*;
    if ty.is_sized(ctx.tcx, names.typing_env()) {
        let is_aligned_logic_sized = Intrinsic::IsAlignedLogicSized.get(ctx);
        return term(ctx, names, args, is_aligned_logic_sized, ctx.mk_args(&[ty.into()]));
    }
    match ty.kind() {
        Slice(t) => {
            let is_aligned_logic_slice = Intrinsic::IsAlignedLogicSlice.get(ctx);
            term(ctx, names, args, is_aligned_logic_slice, ctx.mk_args(&[(*t).into()]))
        }
        Str => Some(Term::true_(ctx.tcx)),
        _ => None,
    }
}

fn metadata_matches_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    //// The type arguments of `metadata_matches`
    subst: GenericArgsRef<'tcx>,
    args: &[Ident],
) -> Option<Term<'tcx>> {
    let param = subst.type_at(0);
    if param.is_sized(ctx.tcx, names.typing_env()) {
        Some(Term::true_(ctx.tcx))
    } else if let TyKind::Slice(ty) = param.kind() {
        let metadata_matches_slice = Intrinsic::MetadataMatchesSlice.get(ctx);
        term(ctx, names, args, metadata_matches_slice, ctx.mk_args(&[(*ty).into()]))
    } else if let TyKind::Str = param.kind() {
        let metadata_matches_str = Intrinsic::MetadataMatchesStr.get(ctx);
        term(ctx, names, args, metadata_matches_str, ctx.mk_args(&[]))
    } else {
        None
    }
}

/// Returns a resolved and normalized term for a dependency.
///
/// Currently, it does not handle invariant axioms but otherwise returns all logical terms.
fn term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    bound: &[Ident],
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    let typing_env = names.typing_env();
    match ctx.intrinsic(def_id) {
        Intrinsic::Resolve => resolve_term(ctx, typing_env, subst, bound),
        Intrinsic::StructuralResolve => {
            structural_resolve(ctx, names, ctx.sig(def_id).inputs[0].0.0, subst.type_at(0))
        }
        Intrinsic::PostconditionOnce => postcondition_once_term(ctx, names, subst, bound),
        Intrinsic::PostconditionMut => postcondition_mut_term(ctx, names, subst, bound),
        Intrinsic::Postcondition => postcondition_term(ctx, names, subst, bound),
        Intrinsic::Precondition => precondition_term(ctx, names, subst, bound),
        Intrinsic::HistInv => fn_mut_hist_inv_term(ctx, typing_env, subst, bound),
        Intrinsic::SizeOfLogic => size_of_logic_term(ctx, typing_env, def_id, subst.type_at(0)),
        Intrinsic::SizeOfValLogic => size_of_val_logic_term(ctx, names, subst, bound),
        Intrinsic::AlignOfLogic => align_of_logic_term(ctx, typing_env, def_id, subst.type_at(0)),
        Intrinsic::IsAlignedLogic => is_aligned_logic_term(ctx, names, subst.type_at(0), bound),
        Intrinsic::MetadataMatches => metadata_matches_term(ctx, names, subst, bound),
        _ => {
            let term = EarlyBinder::bind(ctx.term(def_id).unwrap().rename(bound));
            Some(normalize(ctx, typing_env, term.instantiate(ctx.tcx, subst)))
        }
    }
}
