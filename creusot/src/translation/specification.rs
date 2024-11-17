use crate::{
    contracts_items::{
        creusot_clause_attrs, get_fn_mut_impl_unnest, is_fn_impl_postcond, is_fn_mut_impl_postcond,
        is_fn_mut_impl_unnest, is_fn_once_impl_postcond, is_fn_once_impl_precond,
        is_open_inv_result, is_pearlite,
    },
    ctx::*,
    function::closure_capture_subst,
    naming::anonymous_param_symbol,
    pearlite::TermVisitorMut,
    translation::pearlite::{self, normalize, Literal, Term, TermKind},
    util::erased_identity_for_item,
};
use rustc_hir::{def_id::DefId, AttrArgs, Safety};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{self, Body, Local, SourceInfo, SourceScope, OUTERMOST_SOURCE_SCOPE},
    ty::{EarlyBinder, GenericArg, GenericArgsRef, Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::{
    symbol::{kw, Ident},
    Span, Symbol, DUMMY_SP,
};
use rustc_type_ir::ClosureKind;
use std::{
    collections::{HashMap, HashSet},
    iter,
};

/// A term with an "expl:" label (includes the "expl:" prefix)
#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub struct Condition<'tcx> {
    pub(crate) term: Term<'tcx>,
    /// Label including the "expl:" prefix.
    pub(crate) expl: String,
}

#[derive(Clone, Debug, Default, TypeFoldable, TypeVisitable)]
pub struct PreContract<'tcx> {
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) requires: Vec<Condition<'tcx>>,
    pub(crate) ensures: Vec<Condition<'tcx>>,
    pub(crate) no_panic: bool,
    pub(crate) terminates: bool,
    pub(crate) extern_no_spec: bool,
    /// Are any of the contract clauses here user provided? or merely Creusot inferred / provided?
    pub(crate) has_user_contract: bool,
}

impl<'tcx> PreContract<'tcx> {
    pub(crate) fn subst(&mut self, subst: &HashMap<Symbol, Term<'tcx>>) {
        for term in self.terms_mut() {
            term.subst(subst);
        }
    }

    pub(crate) fn normalize(mut self, tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>) -> Self {
        for term in self.terms_mut() {
            *term =
                normalize(tcx, typing_env, std::mem::replace(term, /*Dummy*/ Term::mk_true(tcx)));
        }
        self
    }

    pub(crate) fn is_requires_false(&self) -> bool {
        self.requires.iter().any(|req| matches!(req.term.kind, TermKind::Lit(Literal::Bool(false))))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.variant.is_none()
    }

    #[allow(dead_code)]
    pub(crate) fn terms(&self) -> impl Iterator<Item = &Term<'tcx>> {
        self.requires
            .iter()
            .chain(self.ensures.iter())
            .map(|cond| &cond.term)
            .chain(self.variant.iter())
    }

    fn terms_mut(&mut self) -> impl Iterator<Item = &mut Term<'tcx>> {
        self.requires
            .iter_mut()
            .chain(self.ensures.iter_mut())
            .map(|cond| &mut cond.term)
            .chain(self.variant.iter_mut())
    }

    pub(crate) fn ensures_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut ensures = self.ensures.clone();

        let postcond = ensures.pop().map_or(Term::mk_true(tcx), |cond| cond.term);
        let postcond =
            ensures.into_iter().rfold(postcond, |postcond, cond| Term::conj(postcond, cond.term));
        postcond
    }

    pub(crate) fn requires_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut requires = self.requires.clone();

        let precond = requires.pop().map_or(Term::mk_true(tcx), |cond| cond.term);
        let precond =
            requires.into_iter().rfold(precond, |precond, cond| Term::conj(precond, cond.term));
        precond
    }
}

/// [ContractClauses] is the most "raw" form of contract we have in Creusot,
/// in this stage, we have only gathered the [DefId]s of the items that hold the various contract
/// expressions.
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct ContractClauses {
    variant: Option<DefId>,
    requires: Vec<DefId>,
    ensures: Vec<DefId>,
    pub(crate) no_panic: bool,
    pub(crate) terminates: bool,
}

impl ContractClauses {
    pub(crate) fn new() -> Self {
        Self {
            variant: None,
            requires: Vec::new(),
            ensures: Vec::new(),
            no_panic: false,
            terminates: false,
        }
    }

    fn get_pre<'tcx>(
        self,
        ctx: &mut TranslationCtx<'tcx>,
        fn_name: &str,
    ) -> EarlyBinder<'tcx, PreContract<'tcx>> {
        let mut out = PreContract::default();
        out.has_user_contract =
            !self.requires.is_empty() || !self.ensures.is_empty() || self.variant.is_some();
        let n_requires = self.requires.len();
        for req_id in self.requires {
            log::trace!("require clause {:?}", req_id);
            let term = ctx.term_fail_fast(req_id).unwrap().clone();
            let expl = if n_requires == 1 {
                format!("expl:{} requires", fn_name)
            } else {
                format!("expl:{} requires #{}", fn_name, out.requires.len())
            };
            out.requires.push(Condition { term, expl });
        }

        let n_ensures = self.ensures.len();
        for ens_id in self.ensures {
            log::trace!("ensures clause {:?}", ens_id);
            let term = ctx.term_fail_fast(ens_id).unwrap().clone();
            let expl = if n_ensures == 1 {
                format!("expl:{} ensures", fn_name)
            } else {
                format!("expl:{} ensures #{}", fn_name, out.ensures.len())
            };
            out.ensures.push(Condition { term, expl });
        }

        if let Some(var_id) = self.variant {
            log::trace!("variant clause {:?}", var_id);
            let term = ctx.term_fail_fast(var_id).unwrap().clone();
            out.variant = Some(term);
        };
        log::trace!("no_panic: {}", self.no_panic);
        out.no_panic = self.no_panic;
        log::trace!("terminates: {}", self.terminates);
        out.terminates = self.terminates;
        EarlyBinder::bind(out)
    }

    pub(crate) fn iter_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).cloned()
    }
}

#[derive(Debug)]
struct ScopeTree<'tcx>(
    HashMap<SourceScope, (HashSet<(Symbol, mir::Place<'tcx>)>, Option<SourceScope>)>,
);

impl<'tcx> ScopeTree<'tcx> {
    fn build(body: &Body<'tcx>) -> Self {
        use rustc_middle::mir::VarDebugInfoContents::Place;
        let mut scope_tree: HashMap<SourceScope, (HashSet<_>, Option<_>)> = Default::default();

        for var_info in &body.var_debug_info {
            // All variables in the DebugVarInfo should be user variables and thus be just places
            // If the variable is local to the function the place will have no projections.
            // Else this is a captured variable.
            let p = match var_info.value {
                Place(p) => p,
                _ => panic!(),
            };
            let info = var_info.source_info;

            let scope = info.scope;
            let scope_data = &body.source_scopes[scope];

            let entry = scope_tree.entry(scope).or_default();

            let name = var_info.name;
            entry.0.insert((name, p));

            if let Some(parent) = scope_data.parent_scope {
                entry.1 = Some(parent);
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }

        for (scope, scope_data) in body.source_scopes.iter_enumerated() {
            if let Some(parent) = scope_data.parent_scope {
                scope_tree.entry(scope).or_default().1 = Some(parent);
                scope_tree.entry(parent).or_default();
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }
        ScopeTree(scope_tree)
    }

    fn visible_places(&self, scope: SourceScope) -> HashMap<Symbol, mir::Place<'tcx>> {
        let mut locals = HashMap::new();
        let mut to_visit = Some(scope);

        while let Some(s) = to_visit.take() {
            let d = (HashSet::new(), None);
            self.0.get(&s).unwrap_or(&d).0.iter().for_each(|(id, loc)| {
                locals.entry(*id).or_insert(*loc);
            });
            to_visit = self.0.get(&s).unwrap_or(&d).1;
        }

        locals
    }
}

// Turn a typing context into a substition.
pub(crate) fn inv_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    locals: &HashMap<Local, Symbol>,
    info: SourceInfo,
) -> HashMap<Symbol, Term<'tcx>> {
    let mut args = HashMap::new();

    let tree = ScopeTree::build(body);

    for (k, p) in tree.visible_places(info.scope) {
        args.insert(k, place_to_term(tcx, p, locals, body));
    }

    args
}

/// Translate a place to a term. The place must represent a single named variable, so it can be
/// - A simple `mir::Local`.
/// - A capture. In this case, the place will simply be a local (the capture's envirnoment)
///   followed by
///   + a `Deref` projection if the closure is FnMut.
///   + a `Field` projection.
///   + a `Deref` projection if the capture is mutable.
fn place_to_term<'tcx>(
    tcx: TyCtxt<'tcx>,
    p: mir::Place<'tcx>,
    locals: &HashMap<Local, Symbol>,
    body: &Body<'tcx>,
) -> Term<'tcx> {
    let ty = p.ty(&body.local_decls, tcx).ty;
    let span = body.local_decls[p.local].source_info.span;
    let mut kind = TermKind::Var(locals[&p.local]);
    for (place_ref, proj) in p.iter_projections() {
        let ty = place_ref.ty(&body.local_decls, tcx).ty;
        match proj {
            mir::ProjectionElem::Deref => {
                let mutable = match ty.kind() {
                    TyKind::Ref(_, _, mutability) => mutability.is_mut(),
                    _ => continue,
                };
                if mutable {
                    kind = TermKind::Cur { term: Box::new(Term { ty, span, kind }) };
                }
            }
            mir::ProjectionElem::Field(field_idx, _) => {
                kind = TermKind::Projection {
                    lhs: Box::new(Term { ty, span, kind }),
                    name: field_idx,
                };
            }
            // The rest are impossible for a place generated by a closure capture.
            // FIXME: is this still true in 2021 (with partial captures) ?
            _ => {
                tcx.dcx().struct_span_err(span, "Partial captures are not supported here").emit();
            }
        };
    }
    Term { ty, span, kind }
}

#[derive(Debug)]
#[allow(dead_code)]
pub enum SpecAttrError {
    InvalidTokens { id: DefId },
    InvalidTerm { id: DefId },
    MultipleVariant { id: DefId },
}

pub(crate) fn contract_clauses_of(
    ctx: &TranslationCtx,
    def_id: DefId,
) -> Result<ContractClauses, SpecAttrError> {
    use SpecAttrError::*;

    let mut contract = ContractClauses::new();

    let get_creusot_item = |arg: &AttrArgs| {
        let predicate_name = match arg {
            AttrArgs::Eq { expr: l, .. } => l.symbol,
            _ => return Err(InvalidTokens { id: def_id }),
        };
        ctx.creusot_item(predicate_name).ok_or(InvalidTerm { id: def_id })
    };

    for arg in creusot_clause_attrs(ctx.tcx, def_id, "requires") {
        contract.requires.push(get_creusot_item(arg)?)
    }

    for arg in creusot_clause_attrs(ctx.tcx, def_id, "ensures") {
        contract.ensures.push(get_creusot_item(arg)?)
    }

    for arg in creusot_clause_attrs(ctx.tcx, def_id, "variant") {
        if std::mem::replace(&mut contract.variant, Some(get_creusot_item(arg)?)).is_some() {
            return Err(MultipleVariant { id: def_id });
        }
    }

    for _ in creusot_clause_attrs(ctx.tcx, def_id, "terminates") {
        contract.terminates = true;
    }

    for _ in creusot_clause_attrs(ctx.tcx, def_id, "no_panic") {
        contract.no_panic = true;
    }

    Ok(contract)
}

pub(crate) fn inherited_extern_spec<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let subst = erased_identity_for_item(ctx.tcx, def_id);
    try {
        if def_id.is_local() || ctx.extern_spec(def_id).is_some() {
            return None;
        }

        let assoc = ctx.opt_associated_item(def_id)?;
        let trait_ref = ctx.impl_trait_ref(assoc.container_id(ctx.tcx))?;
        let id = assoc.trait_item_def_id?;

        if ctx.extern_spec(id).is_none() {
            return None;
        }
        (id, trait_ref.instantiate(ctx.tcx, subst).args)
    }
}

pub(crate) fn contract_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> PreContract<'tcx> {
    let fn_name = ctx.opt_item_name(def_id);
    let fn_name = match &fn_name {
        Some(fn_name) => fn_name.as_str(),
        None => "closure",
    };
    if let Some(extern_spec) = ctx.extern_spec(def_id).cloned() {
        let mut contract =
            extern_spec.contract.get_pre(ctx, fn_name).instantiate(ctx.tcx, extern_spec.subst);
        contract.subst(&extern_spec.arg_subst.iter().cloned().collect());
        // We do NOT normalize the contract here. See below.
        contract
    } else if let Some((parent_id, subst)) = inherited_extern_spec(ctx, def_id) {
        let spec = ctx.extern_spec(parent_id).cloned().unwrap();
        let mut contract = spec.contract.get_pre(ctx, fn_name).instantiate(ctx.tcx, subst);
        contract.subst(&spec.arg_subst.iter().cloned().collect());
        // We do NOT normalize the contract here: indeed, we do not have a valid non-redundant param
        // env for doing this. This is still valid because this contract is going to be substituted
        // and normalized in the caller context (such extern specs are only evaluated in the context
        // of a specific call).
        contract
    } else {
        let subst = erased_identity_for_item(ctx.tcx, def_id);
        let mut contract = contract_clauses_of(ctx, def_id)
            .unwrap()
            .get_pre(ctx, fn_name)
            .instantiate(ctx.tcx, subst);

        if contract.is_empty()
            && !def_id.is_local()
            && ctx.externs.get(def_id.krate).is_none()
            && ctx.item_type(def_id) == ItemType::Program
        {
            contract.extern_no_spec = true;
            contract.requires.push(Condition {
                term: Term::mk_false(ctx.tcx),
                expl: format!("expl:{} requires false", fn_name),
            });
        }

        contract.normalize(ctx.tcx, ctx.typing_env(def_id))
    }
}

#[derive(TypeVisitable, TypeFoldable, Debug, Clone)]
pub struct PreSignature<'tcx> {
    pub(crate) inputs: Vec<(Symbol, Span, Ty<'tcx>)>,
    pub(crate) output: Ty<'tcx>,
    pub(crate) contract: PreContract<'tcx>,
    // trusted: bool,
    // span: Span,
    // program: bool,
}

impl<'tcx> PreSignature<'tcx> {
    pub(crate) fn normalize(mut self, tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>) -> Self {
        self.contract = self.contract.normalize(tcx, typing_env);
        self
    }
}

pub(crate) fn pre_sig_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> PreSignature<'tcx> {
    let (inputs, output) = inputs_and_output(ctx.tcx, def_id);

    let mut contract = crate::specification::contract_of(ctx, def_id);

    let fn_ty = ctx.tcx.type_of(def_id).instantiate_identity();

    if let TyKind::Closure(_, subst) = fn_ty.kind() {
        let self_ = Symbol::intern("_1");
        let kind = subst.as_closure().kind();
        let env_ty = ctx.closure_env_ty(fn_ty, kind, ctx.lifetimes.re_erased);

        let self_pre =
            if env_ty.is_ref() { Term::var(self_, env_ty).cur() } else { Term::var(self_, env_ty) };

        let mut pre_subst =
            closure_capture_subst(ctx, def_id, subst, false, None, self_pre.clone());
        for pre in &mut contract.requires {
            pre_subst.visit_mut_term(&mut pre.term);
        }

        if kind == ClosureKind::FnMut {
            let args = subst.as_closure().sig().inputs().skip_binder()[0];
            let unnest_subst =
                ctx.mk_args(&[GenericArg::from(args), GenericArg::from(env_ty.peel_refs())]);

            let unnest_id = get_fn_mut_impl_unnest(ctx.tcx);

            let term = Term::call(
                ctx.tcx,
                ctx.typing_env(def_id),
                unnest_id,
                unnest_subst,
                vec![Term::var(self_, env_ty).cur(), Term::var(self_, env_ty).fin()],
            );
            let expl = "expl:closure unnest".to_string();
            contract.ensures.push(Condition { term, expl });
        };

        let self_post = match kind {
            ClosureKind::Fn => Term::var(self_, env_ty).cur(),
            ClosureKind::FnMut => Term::var(self_, env_ty).fin(),
            ClosureKind::FnOnce => Term::var(self_, env_ty),
        };

        let mut post_subst =
            closure_capture_subst(ctx, def_id, subst, !env_ty.is_ref(), Some(self_pre), self_post);

        for post in &mut contract.ensures {
            post_subst.visit_mut_term(&mut post.term);
        }

        if let Some(span) = post_subst.use_of_consumed_var_error
            && kind == ClosureKind::FnOnce
        {
            ctx.fatal_error(
                span,
                "Use of a closure capture in a post-condition, but it is consumed by the closure.",
            )
            .emit()
        }

        assert!(contract.variant.is_none());
    }

    let mut inputs: Vec<_> = inputs
        .enumerate()
        .map(|(idx, (ident, ty))| {
            if ident.name.as_str() == "result"
                && !is_fn_impl_postcond(ctx.tcx, def_id)
                && !is_fn_mut_impl_postcond(ctx.tcx, def_id)
                && !is_fn_once_impl_postcond(ctx.tcx, def_id)
                && !is_fn_mut_impl_unnest(ctx.tcx, def_id)
                && !is_fn_once_impl_precond(ctx.tcx, def_id)
            {
                ctx.crash_and_error(ident.span, "`result` is not allowed as a parameter name")
            }

            let name = if ident.name.as_str().is_empty() {
                anonymous_param_symbol(idx)
            } else {
                ident.name
            };
            (name, ident.span, ty)
        })
        .collect();
    if ctx.type_of(def_id).instantiate_identity().is_fn() && inputs.is_empty() {
        inputs.push((kw::Empty, DUMMY_SP, ctx.tcx.types.unit));
    };

    if !is_pearlite(ctx.tcx, def_id) {
        // Type invariants

        let fn_name = ctx.opt_item_name(def_id);
        let fn_name = match &fn_name {
            Some(fn_name) => fn_name.as_str(),
            None => "closure",
        };
        let subst = erased_identity_for_item(ctx.tcx, def_id);

        let params_open_inv: HashSet<usize> = ctx
            .params_open_inv(def_id)
            .iter()
            .copied()
            .flatten()
            .map(|&i| if ctx.tcx.is_closure_like(def_id) { i + 1 } else { i })
            .collect();
        let mut requires = Vec::new();
        for (i, (name, span, ty)) in inputs.iter().enumerate() {
            if params_open_inv.contains(&i) {
                continue;
            }
            if let Some(term) = pearlite::type_invariant_term(ctx, def_id, *name, *span, *ty) {
                let term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
                let expl = format!("expl:{} '{}' type invariant", fn_name, name);
                requires.push(Condition { term, expl });
            }
        }
        requires.append(&mut contract.requires);
        contract.requires = requires;

        let ret_ty_span: Option<Span> =
            try { ctx.tcx.hir().get_fn_output(def_id.as_local()?)?.span() };
        if !is_open_inv_result(ctx.tcx, def_id)
            && let Some(term) = pearlite::type_invariant_term(
                ctx,
                def_id,
                Symbol::intern("result"),
                ret_ty_span.unwrap_or_else(|| ctx.tcx.def_span(def_id)),
                output,
            )
        {
            let term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
            let expl = format!("expl:{} result type invariant", fn_name);
            contract.ensures.insert(0, Condition { term, expl });
        }
    }

    PreSignature { inputs, output, contract }
}

fn inputs_and_output(tcx: TyCtxt, def_id: DefId) -> (impl Iterator<Item = (Ident, Ty)>, Ty) {
    let ty = tcx.type_of(def_id).instantiate_identity();
    let (inputs, output): (Box<dyn Iterator<Item = (rustc_span::symbol::Ident, _)>>, _) = match ty
        .kind()
    {
        TyKind::FnDef(..) => {
            let gen_sig = tcx
                .instantiate_bound_regions_with_erased(tcx.fn_sig(def_id).instantiate_identity());
            let sig =
                tcx.normalize_erasing_regions(TypingEnv::non_body_analysis(tcx, def_id), gen_sig);
            let iter = tcx.fn_arg_names(def_id).iter().cloned().zip(sig.inputs().iter().cloned());
            (Box::new(iter), sig.output())
        }
        TyKind::Closure(_, subst) => {
            let sig = tcx.instantiate_bound_regions_with_erased(
                tcx.signature_unclosure(subst.as_closure().sig(), Safety::Safe),
            );
            let sig = tcx.normalize_erasing_regions(TypingEnv::non_body_analysis(tcx, def_id), sig);
            let env_ty = tcx.closure_env_ty(ty, subst.as_closure().kind(), tcx.lifetimes.re_erased);

            // I wish this could be called "self"
            let closure_env = (Ident::empty(), env_ty);
            let names = tcx
                .fn_arg_names(def_id)
                .iter()
                .cloned()
                .chain(iter::repeat(rustc_span::symbol::Ident::empty()));
            (
                Box::new(iter::once(closure_env).chain(names.zip(sig.inputs().iter().cloned()))),
                sig.output(),
            )
        }
        _ => (Box::new(iter::empty()), tcx.type_of(def_id).instantiate_identity()),
    };
    (inputs, output)
}
