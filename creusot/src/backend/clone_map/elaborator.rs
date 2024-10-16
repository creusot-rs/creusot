use super::{CloneNames, Dependency, Kind};
use crate::{
    backend::{
        dependency::ClosureSpecKind,
        logic::{lower_logical_defn, lower_pure_defn, sigs, spec_axiom},
        program,
        signature::named_sig_to_why3,
        structural_resolve::structural_resolve,
        term::lower_pure,
        ty::translate_ty,
        ty_inv::InvariantElaborator,
        TransId, Why3Generator,
    },
    ctx::*,
    options::SpanMode,
    traits,
    translation::{
        pearlite::{normalize, Term},
        specification::PreContract,
    },
    util::{self, get_builtin, ident_of, PreSignature},
};
use indexmap::IndexSet;
use rustc_middle::ty::{self, Const, EarlyBinder, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable};
use rustc_span::{Span, Symbol, DUMMY_SP};
use why3::{
    declaration::{Attribute, Axiom, Constant, Contract, Decl, LetKind, Signature, Use, ValDecl},
    exp::Binder,
    QName,
};

/// The symbol elaborator expands required definitions as symbols and definitions, effectively performing the clones itself.
pub(super) struct SymbolElaborator<'tcx> {
    used_types: IndexSet<Symbol>,
    param_env: ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> SymbolElaborator<'tcx> {
    pub fn new(param_env: ParamEnv<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { used_types: Default::default(), param_env, tcx }
    }

    pub fn build_clone(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut Dependencies<'tcx>,
        item: Dependency<'tcx>,
        level_of_item: CloneLevel,
    ) -> Vec<Decl> {
        let param_env = names.param_env(ctx);
        let old_names = names;
        let mut names = ImmutDeps {
            tcx: ctx.tcx,
            param_env,
            names: &mut old_names.names,
            span_mode: ctx.opts.span_mode.clone(),
        };
        let names = &mut names;

        match item {
            Dependency::Type(ty) => self.elaborate_ty(ctx, names, ty),
            Dependency::Builtin(b) => {
                vec![Decl::UseDecl(Use { name: b.qname(), as_: None, export: false })]
            }
            Dependency::TyInvAxiom(ty) => {
                let mut elab = InvariantElaborator::new(param_env, ctx);
                if let Some(term) = elab.elaborate_inv(ty, false) {
                    let rewrite = elab.rewrite;
                    let exp = lower_pure(ctx, names, &term);
                    let axiom = Axiom { name: names.insert(item).ident(), rewrite, axiom: exp };
                    vec![Decl::Axiom(axiom)]
                } else {
                    vec![]
                }
            }
            Dependency::Item(_, _) | Dependency::ClosureSpec(_, _, _) => {
                self.elaborate_item(ctx, names, param_env, level_of_item, item)
            }
            Dependency::StructuralResolve(ty) => {
                let (binder, term) = structural_resolve(ctx, ty);

                let exp = if let Some(mut term) = term {
                    normalize(ctx.tcx, param_env, &mut term);
                    Some(lower_pure(ctx, names, &term))
                } else {
                    None
                };

                let binder =
                    Binder::typed(ident_of(binder.0), translate_ty(ctx, names, DUMMY_SP, binder.1));
                let sig = Signature {
                    name: names.insert(item).ident(),
                    trigger: None,
                    attrs: vec![],
                    retty: None,
                    args: vec![binder],
                    contract: Contract::default(),
                };

                let pred = Decl::predicate(sig, exp);

                vec![pred]
            }
        }
    }

    fn elaborate_ty(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut ImmutDeps<'_, 'tcx>,
        ty: Ty<'tcx>,
    ) -> Vec<Decl> {
        let Some((def_id, subst)) = Dependency::Type(ty).did() else { return Vec::new() };

        match ty.kind() {
            TyKind::Alias(_, _) => vec![ctx.assoc_ty_decl(names, def_id, subst)],
            _ => {
                if let Some(why3_modl) = util::get_builtin(ctx.tcx, def_id) {
                    let qname = QName::from_string(why3_modl.as_str());
                    let Kind::Used(modl, _) = names.insert(Dependency::Type(ty)) else {
                        return vec![];
                    };

                    self.used_types
                        .insert(modl)
                        .then(|| {
                            let use_decl =
                                Use { as_: None, name: qname.module_qname(), export: false };

                            vec![Decl::UseDecl(use_decl)]
                        })
                        .unwrap_or_default()
                } else {
                    self.emit_use(names, Dependency::Type(ty))
                }
            }
        }
    }

    fn emit_use(&mut self, names: &mut ImmutDeps<'_, 'tcx>, dep: Dependency<'tcx>) -> Vec<Decl> {
        if let k @ Kind::Used(modl, _) = names.insert(dep) {
            self.used_types
                .insert(modl)
                .then(|| {
                    let qname = k.qname();
                    let name = qname.module_qname();
                    let mut did = dep.did().unwrap().0;
                    if util::item_type(self.tcx, did) == ItemType::Field {
                        did = self.tcx.parent(did);
                    };

                    let modl = if util::item_type(self.tcx, did) == ItemType::Closure {
                        Symbol::intern(&format!("{}_Type", module_name(self.tcx, did)))
                    } else {
                        module_name(self.tcx, did)
                    };

                    let use_decl =
                        Use { as_: Some(name.clone()), name: modl.as_str().into(), export: false };
                    vec![Decl::UseDecl(use_decl)]
                })
                .unwrap_or_default()
        } else {
            vec![]
        }
    }

    fn elaborate_item(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut ImmutDeps<'_, 'tcx>,
        param_env: ParamEnv<'tcx>,
        level_of_item: CloneLevel,
        item: Dependency<'tcx>,
    ) -> Vec<Decl> {
        let Some((def_id, subst)) = item.did() else { unreachable!("{item:?}") };

        if let Some(b) = get_builtin(ctx.tcx, def_id) {
            return vec![Decl::UseDecl(Use {
                name: QName::from_string(b.as_str()).module_qname(),
                as_: None,
                export: false,
            })];
        }

        if let Kind::Used(_, _) = names.get(item) {
            return self.emit_use(names, item);
        };

        let mut pre_sig =
            EarlyBinder::bind(sig(ctx, self.param_env, item)).instantiate(ctx.tcx, subst);
        pre_sig = pre_sig.normalize(ctx.tcx, param_env);

        let is_accessor =
            item.to_trans_id(self.tcx, self.param_env).is_some_and(|i| ctx.is_accessor(i));
        let kind = if item.is_closure_spec() {
            if is_accessor {
                Some(LetKind::Function)
            } else {
                Some(LetKind::Predicate)
            }
        } else {
            util::item_type(ctx.tcx, def_id).let_kind()
        };

        if CloneLevel::Signature == level_of_item {
            pre_sig.contract = PreContract::default();
        }

        let name = if let Dependency::ClosureSpec(_, _, _) = item {
            names.insert(item).ident()
        } else {
            names.value(def_id, subst).as_ident()
        };

        let mut sig = named_sig_to_why3(ctx, names, name, &pre_sig, def_id);

        if CloneLevel::Signature == level_of_item {
            return val(ctx, sig, kind);
        } else if CloneLevel::Contract == level_of_item {
            return val(ctx, sig, kind);
        };

        if util::is_resolve_function(ctx.tcx, def_id) {
            let trait_meth_id =
                ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
            let arg = Term::var(pre_sig.inputs[0].0, pre_sig.inputs[0].2);
            let body;

            if let TyKind::Closure(..) = subst[0].as_type().unwrap().kind() {
                // Closures have a special instance of Resolve
                body = Term::call(ctx.tcx, trait_meth_id, subst, vec![arg]);
            } else {
                match traits::resolve_assoc_item_opt(ctx.tcx, param_env, trait_meth_id, subst) {
                    traits::TraitResol::Instance(meth_did, meth_substs) => {
                        // We know the instance => body points to it
                        body = Term::call(ctx.tcx, meth_did, meth_substs, vec![arg]);
                    }
                    traits::TraitResol::UnknownFound | traits::TraitResol::UnknownNotFound => {
                        // We don't know the instance => body is opaque
                        sig.retty = None;
                        return vec![Decl::predicate(sig, None)];
                    }
                    traits::TraitResol::NoInstance => {
                        // We know there is no instance => body is true
                        body = Term::mk_true(ctx.tcx);
                    }
                }
            }

            lower_logical_defn(ctx, names, sig, kind, body)
        } else if item.is_closure_spec() || ctx.is_logical(def_id) {
            let Some(term) = term(ctx, param_env, item) else { return Vec::new() };
            let mut term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
            normalize(ctx.tcx, param_env, &mut term);
            if is_accessor {
                lower_logical_defn(ctx, names, sig, kind, term)
            } else if item.is_closure_spec() {
                // TODO: Clean this up and merge with previous branches
                lower_pure_defn(ctx, names, sig, kind, false, term)
            } else {
                lower_logical_defn(ctx, names, sig, kind, term)
            }
        } else if util::item_type(ctx.tcx, def_id) == ItemType::Constant {
            let uneval = ty::UnevaluatedConst::new(def_id, subst);
            let constant = Const::new(ctx.tcx, ty::ConstKind::Unevaluated(uneval));
            let ty = ctx.type_of(def_id).instantiate_identity();

            let span = ctx.def_span(def_id);
            let res = crate::constant::from_ty_const(&mut ctx.ctx, constant, ty, param_env, span);

            let res = lower_pure(ctx, names, &res);
            vec![Decl::ConstantDecl(Constant {
                type_: sig.retty.unwrap(),
                name: sig.name,
                body: Some(res),
            })]
        } else if util::is_ghost_closure(ctx.tcx, def_id) {
            // Inline the body of ghost closures
            let mut coma = program::to_why(
                ctx,
                names,
                BodyId { def_id: def_id.expect_local(), promoted: None },
            );
            coma.name = sig.name;
            vec![Decl::Coma(coma)]

            // TODO: this works for ghost closure, because we know they will not get passed
            // to a function like `map`.
            // If we want to inline arbitrary contract-less closure, we need to add `[@coma:extspec]`
            // and to use the resulting pre and post.
        } else {
            val(ctx, sig, kind)
        }
    }
}

fn val<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    mut sig: Signature,
    kind: Option<LetKind>,
) -> Vec<Decl> {
    sig.contract.variant = Vec::new();
    if let Some(k) = kind {
        let ax = if !sig.contract.is_empty() { Some(spec_axiom(&sig)) } else { None };

        let (mut sig, _) = sigs(ctx, sig);
        if let LetKind::Predicate = k {
            sig.retty = None;
        };

        if let LetKind::Constant = k {
            return vec![Decl::ValDecl(ValDecl { ghost: false, val: false, kind, sig })];
        }

        let mut d = vec![Decl::ValDecl(ValDecl { ghost: false, val: false, kind, sig })];

        if let Some(ax) = ax {
            d.push(Decl::Axiom(ax))
        }
        d
    } else {
        vec![program::val(ctx, sig)]
    }
}

fn term<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    param_env: ParamEnv<'tcx>,
    dep: Dependency<'tcx>,
) -> Option<Term<'tcx>> {
    ctx.term(dep.to_trans_id(ctx.tcx, param_env)?).cloned()
}

fn sig<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    param_env: ParamEnv<'tcx>,
    dep: Dependency<'tcx>,
) -> PreSignature<'tcx> {
    match dep.to_trans_id(ctx.tcx, param_env).unwrap() {
        TransId::Item(id) => ctx.sig(id).clone(),

        TransId::Hacked(h_id, id) => match h_id {
            ClosureSpecKind::PostconditionOnce => {
                ctx.closure_contract(id).postcond_once.as_ref().unwrap().0.clone()
            }
            ClosureSpecKind::PostconditionMut => {
                ctx.closure_contract(id).postcond_mut.as_ref().unwrap().0.clone()
            }
            ClosureSpecKind::Postcondition => {
                ctx.closure_contract(id).postcond.as_ref().unwrap().0.clone()
            }
            ClosureSpecKind::Precondition => ctx.closure_contract(id).precond.0.clone(),
            ClosureSpecKind::Unnest => ctx.closure_contract(id).unnest.as_ref().unwrap().0.clone(),
            ClosureSpecKind::Resolve => ctx.closure_contract(id).resolve.0.clone(),
            ClosureSpecKind::Accessor(ix) => {
                ctx.closure_contract(id).accessors[ix as usize].0.clone()
            }
        },
        // In future change this
        TransId::TyInvAxiom(_) | TransId::StructuralResolve(_) => unreachable!(),
    }
}

/// ImmutDeps works like `clone_map::Dependencies` but is immutable: if you ask it to name
/// something that isn't already in the graph, it will crash the whole compilation.
/// At the time of elaboration, we expect the whole graph to have been calculated.
struct ImmutDeps<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    names: &'a mut CloneNames<'tcx>,
    param_env: ParamEnv<'tcx>,
    span_mode: SpanMode,
}

impl<'a, 'tcx> ImmutDeps<'a, 'tcx> {
    fn get(&self, ix: Dependency<'tcx>) -> &Kind {
        let n = self.tcx.try_normalize_erasing_regions(self.param_env, ix).unwrap_or(ix);
        self.names.names.get(&n).unwrap_or_else(|| {
            panic!("Could not find {ix:?} -> {n:?}");
        })
    }
}

impl<'a, 'tcx> Namer<'tcx> for ImmutDeps<'a, 'tcx> {
    fn insert(&mut self, ix: Dependency<'tcx>) -> Kind {
        *self.get(ix)
    }

    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        _: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T {
        self.tcx.try_normalize_erasing_regions(self.param_env, ty).unwrap_or(ty)
    }

    fn import_prelude_module(&mut self, _: PreludeModule) {
        ()
    }

    fn with_vis<F, A>(&mut self, _: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        f(self)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn span(&mut self, span: Span) -> Option<Attribute> {
        if span.is_dummy() {
            return None;
        }

        let lo = self.tcx.sess.source_map().lookup_char_pos(span.lo());
        let rustc_span::FileName::Real(path) = &lo.file.name else { return None };
        match (&self.span_mode, path) {
            (SpanMode::Relative(_), rustc_span::RealFileName::Remapped { .. }) => return None,
            _ => (),
        };

        let cnt = self.names.spans.len();
        let name =
            self.names.spans.entry(span).or_insert_with(|| Symbol::intern(&format!("span{cnt}")));
        Some(Attribute::NamedSpan(name.to_string()))
    }
}
