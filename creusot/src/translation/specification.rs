use crate::{
    backend::closures::ClosSubst,
    contracts_items::{
        Intrinsic, creusot_clause_attrs, is_check_ghost, is_check_terminates, is_logic,
        is_open_inv_result,
    },
    ctx::*,
    naming::{name, variable_name},
    translation::pearlite::{
        Ident, Literal, PIdent, Term, TermKind, TermVisitorMut, normalize, type_invariant_term,
    },
    util::erased_identity_for_item,
};
use rustc_ast::Mutability;
use rustc_hir::{AttrArgs, Safety, def::DefKind, def_id::DefId};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    thir::{BodyTy, Pat, PatKind, Thir},
    ty::{EarlyBinder, GenericArg, GenericArgsRef, Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::{DUMMY_SP, Span};
use rustc_type_ir::ClosureKind;
use std::{collections::HashSet, iter::repeat};

/// A term with an "expl:" label (includes the "expl:" prefix)
#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub struct Condition<'tcx> {
    pub(crate) term: Term<'tcx>,
    /// Label including the "expl:" prefix.
    #[type_visitable(ignore)]
    #[type_foldable(identity)]
    pub(crate) expl: String,
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub struct PreContract<'tcx> {
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) requires: Vec<Condition<'tcx>>,
    pub(crate) ensures: Vec<Condition<'tcx>>,
    pub(crate) check_ghost: bool,
    pub(crate) check_terminates: bool,
    pub(crate) extern_no_spec: bool,
    /// Are any of the contract clauses here user provided? or merely Creusot inferred / provided?
    pub(crate) has_user_contract: bool,
}

impl<'tcx> PreContract<'tcx> {
    pub(crate) fn normalize(
        mut self,
        ctx: &TranslationCtx<'tcx>,
        typing_env: TypingEnv<'tcx>,
    ) -> Self {
        for term in self
            .requires
            .iter_mut()
            .chain(self.ensures.iter_mut())
            .map(|cond| &mut cond.term)
            .chain(self.variant.iter_mut())
        {
            *term =
                normalize(ctx, typing_env, std::mem::replace(term, /*Dummy*/ Term::true_(ctx.tcx)));
        }
        self
    }

    pub(crate) fn is_requires_false(&self) -> bool {
        self.requires.iter().any(|req| matches!(req.term.kind, TermKind::Lit(Literal::Bool(false))))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.variant.is_none()
    }

    pub(crate) fn ensures_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut ensures = self.ensures.clone();

        let postcond = ensures.pop().map_or(Term::true_(tcx), |cond| cond.term);
        ensures.into_iter().rfold(postcond, |postcond, cond| Term::conj(postcond, cond.term))
    }

    pub(crate) fn requires_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut requires = self.requires.clone();

        let precond = requires.pop().map_or(Term::true_(tcx), |cond| cond.term);
        requires.into_iter().rfold(precond, |precond, cond| Term::conj(precond, cond.term))
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
    pub(crate) check_ghost: bool,
    pub(crate) check_terminates: bool,
}

impl ContractClauses {
    pub(crate) fn new() -> Self {
        Self {
            variant: None,
            requires: Vec::new(),
            ensures: Vec::new(),
            check_ghost: false,
            check_terminates: false,
        }
    }

    fn get_pre<'tcx>(
        self,
        ctx: &TranslationCtx<'tcx>,
        fn_name: &str,
        bound: impl IntoIterator<Item = Ident>,
    ) -> EarlyBinder<'tcx, PreContract<'tcx>> {
        let bound_with_result =
            &bound.into_iter().chain(std::iter::once(name::result())).collect::<Box<_>>();
        let bound = bound_with_result.split_last().unwrap().1;
        let has_user_contract =
            !self.requires.is_empty() || !self.ensures.is_empty() || self.variant.is_some();
        let n_requires = self.requires.len();
        let requires = self
            .requires
            .into_iter()
            .enumerate()
            .map(|(i, req_id)| {
                log::trace!("require clause {:?}", req_id);
                let mut expl = format!("expl:{fn_name} requires");
                if n_requires > 1 {
                    expl.push_str(&format!(" #{i}"))
                }
                Condition { term: ctx.term(req_id).unwrap().rename(bound), expl }
            })
            .collect();

        let n_ensures = self.ensures.len();
        let ensures = self
            .ensures
            .into_iter()
            .enumerate()
            .map(|(i, ens_id)| {
                log::trace!("ensures clause {:?}", ens_id);
                let mut expl = format!("expl:{fn_name} ensures");
                if n_ensures > 1 {
                    expl.push_str(&format!(" #{i}"))
                }
                Condition { term: ctx.term(ens_id).unwrap().rename(bound_with_result), expl }
            })
            .collect();

        let variant = self.variant.map(|var_id| {
            log::trace!("variant clause {:?}", var_id);
            ctx.term(var_id).unwrap().rename(bound)
        });
        log::trace!("ghost: {}", self.check_ghost);
        log::trace!("terminates: {}", self.check_terminates);
        EarlyBinder::bind(PreContract {
            variant,
            requires,
            ensures,
            check_ghost: self.check_ghost,
            check_terminates: self.check_terminates,
            extern_no_spec: false,
            has_user_contract,
        })
    }
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

    let get_creusot_item = |arg: &AttrArgs| {
        let predicate_name = match arg {
            AttrArgs::Eq { expr: l, .. } => l.symbol,
            _ => return Err(InvalidTokens { id: def_id }),
        };
        ctx.creusot_item(predicate_name).ok_or(InvalidTerm { id: def_id })
    };

    let requires = creusot_clause_attrs(ctx.tcx, def_id, "requires")
        .map(get_creusot_item)
        .collect::<Result<Vec<_>, _>>()?;
    let ensures = creusot_clause_attrs(ctx.tcx, def_id, "ensures")
        .map(get_creusot_item)
        .collect::<Result<Vec<_>, _>>()?;
    let mut it_variant = creusot_clause_attrs(ctx.tcx, def_id, "variant").map(get_creusot_item);
    let variant = it_variant.next().transpose()?;
    if it_variant.next().transpose()?.is_some() {
        return Err(MultipleVariant { id: def_id });
    }
    let check_terminates = is_check_terminates(ctx.tcx, def_id);
    let check_ghost = is_check_ghost(ctx.tcx, def_id);

    Ok(ContractClauses { requires, ensures, variant, check_terminates, check_ghost })
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

pub(crate) fn contract_of<'tcx>(ctx: &TranslationCtx<'tcx>, def_id: DefId) -> PreSignature<'tcx> {
    let fn_name = ctx.opt_item_name(def_id);
    let fn_name = match &fn_name {
        Some(fn_name) => fn_name.as_str(),
        None => "closure",
    };

    let (inputs, output) = inputs_and_output(ctx.tcx, def_id);
    // TODO: handle the "self" argument better
    let raw_inputs =
        if !inputs.is_empty() && inputs[0].0.0 == name::self_() { &inputs[1..] } else { &inputs };
    let bound = raw_inputs.iter().map(|(ident, _, _)| ident.0);
    let subst = erased_identity_for_item(ctx.tcx, def_id);
    let mut contract = contract_clauses_of(ctx, def_id)
        .unwrap()
        .get_pre(ctx, fn_name, bound)
        .instantiate(ctx.tcx, subst);

    if let Some(spec) = ctx.extern_spec(def_id).cloned() {
        // We do NOT normalize the contract here. See below.
        let bound = spec.inputs.iter().map(|(ident, _, _)| ident.0);
        let contract = spec.contract.get_pre(ctx, fn_name, bound).instantiate(ctx.tcx, spec.subst);
        PreSignature {
            inputs: EarlyBinder::bind(spec.inputs).instantiate(ctx.tcx, spec.subst),
            output: EarlyBinder::bind(spec.output).instantiate(ctx.tcx, spec.subst),
            contract,
        }
    } else if contract.is_empty()
        && let Some((parent_id, subst)) = inherited_extern_spec(ctx, def_id)
    {
        let spec = ctx.extern_spec(parent_id).cloned().unwrap();
        let bound = spec.inputs.iter().map(|(ident, _, _)| ident.0);
        // We do NOT normalize the contract here: indeed, we do not have a valid non-redundant param
        // env for doing this. This is still valid because this contract is going to be substituted
        // and normalized in the caller context (such extern specs are only evaluated in the context
        // of a specific call).
        let contract = spec.contract.get_pre(ctx, fn_name, bound).instantiate(ctx.tcx, subst);
        PreSignature {
            inputs: EarlyBinder::bind(spec.inputs).instantiate(ctx.tcx, subst),
            output: EarlyBinder::bind(spec.output).instantiate(ctx.tcx, subst),
            contract,
        }
    } else {
        if contract.is_empty()
            && !def_id.is_local()
            && ctx.externs.get(def_id.krate).is_none()
            && ctx.item_type(def_id) == ItemType::Program
        {
            contract.extern_no_spec = true;
            contract.requires.push(Condition {
                term: Term::false_(ctx.tcx),
                expl: format!("expl:{} requires false", fn_name),
            });
        }
        let contract = contract.normalize(ctx, ctx.typing_env(def_id));
        PreSignature { inputs, output, contract }
    }
}

/// A function signature, that can be either program or logic.
#[derive(TypeVisitable, TypeFoldable, Debug, Clone)]
pub(crate) struct PreSignature<'tcx> {
    pub(crate) inputs: Box<[(PIdent, Span, Ty<'tcx>)]>,
    pub(crate) output: Ty<'tcx>,
    pub(crate) contract: PreContract<'tcx>,
}

impl<'tcx> PreSignature<'tcx> {
    pub(crate) fn normalize(
        mut self,
        ctx: &TranslationCtx<'tcx>,
        typing_env: TypingEnv<'tcx>,
    ) -> Self {
        self.contract = self.contract.normalize(ctx, typing_env);
        self
    }

    pub(crate) fn add_type_invariant_spec(
        &mut self,
        ctx: &TranslationCtx<'tcx>,
        def_id: DefId,
        typing_env: TypingEnv<'tcx>,
    ) {
        let fn_name = ctx.opt_item_name(def_id);
        let fn_name = match &fn_name {
            Some(fn_name) => fn_name.as_str(),
            None => "closure",
        };

        let params_open_inv: HashSet<usize> = ctx
            .params_open_inv(def_id)
            .iter()
            .copied()
            .flatten()
            .map(|&i| if ctx.is_closure_like(def_id) { i + 1 } else { i })
            .collect();

        let new_requires = self.inputs.iter().enumerate().filter_map(|(i, (ident, span, ty))| {
            if !params_open_inv.contains(&i)
                && let Some(term) = type_invariant_term(ctx, typing_env, ident.0, *span, *ty)
            {
                let expl =
                    format!("expl:{} '{}' type invariant", fn_name, ident.0.name().to_string());
                Some(Condition { term, expl })
            } else {
                None
            }
        });
        self.contract.requires.splice(0..0, new_requires);

        let ret_ty_span: Option<Span> = try { ctx.hir_get_fn_output(def_id.as_local()?)?.span() };
        if (ctx.def_kind(def_id) == DefKind::ConstParam || !is_open_inv_result(ctx.tcx, def_id))
            && let Some(term) = type_invariant_term(
                ctx,
                typing_env,
                name::result(),
                ret_ty_span.unwrap_or_else(|| ctx.def_span(def_id)),
                self.output,
            )
        {
            let expl = format!("expl:{} result type invariant", fn_name);
            self.contract.ensures.insert(0, Condition { term, expl });
        }
    }
}

pub(crate) fn pre_sig_of<'tcx>(ctx: &TranslationCtx<'tcx>, def_id: DefId) -> PreSignature<'tcx> {
    if ctx.def_kind(def_id) == DefKind::ConstParam {
        let contract = PreContract {
            variant: None,
            requires: vec![],
            ensures: vec![],
            check_ghost: true,
            check_terminates: true,
            extern_no_spec: false,
            has_user_contract: false,
        };
        let output = ctx.type_of(def_id).no_bound_vars().unwrap();
        return PreSignature { inputs: Box::new([]), output, contract };
    }

    let mut presig = contract_of(ctx, def_id);

    if ctx.def_kind(def_id) == DefKind::Closure {
        let fn_ty = ctx.type_of(def_id).instantiate_identity();
        let TyKind::Closure(_, subst) = fn_ty.kind() else { unreachable!() };

        let kind = subst.as_closure().kind();
        let env_ty = ctx.closure_env_ty(fn_ty, kind, ctx.lifetimes.re_erased);
        let self_ = Term::var(name::self_(), env_ty);

        let self_pre = match kind {
            ClosureKind::Fn => self_.clone().shr_deref(),
            ClosureKind::FnMut => self_.clone().cur(),
            ClosureKind::FnOnce => self_.clone(),
        };

        let mut pre_subst = ClosSubst::pre(ctx, def_id.expect_local(), self_pre.clone());
        for pre in &mut presig.contract.requires {
            pre_subst.visit_mut_term(&mut pre.term);
        }

        let mut post_subst = if kind == ClosureKind::FnOnce {
            // If this is an FnOnce closure, then variables captured by value
            // are consumed by the closure, and thus we cannot refer to them in
            // the post state.
            let post_owned_projs = repeat(None);
            ClosSubst::post_owned(ctx, def_id.expect_local(), self_pre, post_owned_projs)
        } else {
            let self_post =
                if kind == ClosureKind::Fn { self_pre.clone() } else { self_.clone().fin() };
            ClosSubst::post_ref(ctx, def_id.expect_local(), self_pre, self_post)
        };

        for post in &mut presig.contract.ensures {
            post_subst.visit_mut_term(&mut post.term);
        }

        if kind == ClosureKind::FnMut {
            let args = subst.as_closure().sig().inputs().map_bound(|tys| tys[0]);
            let args = ctx.instantiate_bound_regions_with_erased(args);

            let term = Term::call(
                ctx.tcx,
                ctx.typing_env(def_id),
                Intrinsic::HistInv.get(ctx),
                ctx.mk_args(&[args, env_ty.peel_refs()].map(GenericArg::from)),
                [self_.clone().cur(), self_.fin()],
            );
            let expl = "expl:closure hist_inv post".to_string();
            presig.contract.ensures.push(Condition { term, expl });
        };

        assert!(presig.contract.variant.is_none());
    }

    if !presig.contract.extern_no_spec {
        for (input, _, _) in &presig.inputs {
            if input.0.name() == why3::Symbol::intern("result")
                && !matches!(
                    ctx.intrinsic(def_id),
                    Intrinsic::Postcondition
                        | Intrinsic::PostconditionMut
                        | Intrinsic::PostconditionOnce
                        | Intrinsic::HistInv
                        | Intrinsic::Precondition
                )
            {
                ctx.crash_and_error(
                    ctx.def_span(def_id),
                    "`result` is not allowed as a parameter name",
                )
            }
        }
    }

    presig
}

pub fn inputs_and_output_from_thir<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    thir: &Thir<'tcx>,
) -> (Box<[(PIdent, Span, Ty<'tcx>)]>, Ty<'tcx>) {
    match thir.body_type {
        BodyTy::Const(ty) => ([].into(), ty),
        BodyTy::Fn(fn_sig) => {
            let inputs = thir
                .params
                .iter()
                .skip(if ctx.tcx.is_closure_like(def_id) { 1 } else { 0 })
                .enumerate()
                .map(|(ix, param)| match &param.pat {
                    Some(box Pat { kind, span, ty }) => {
                        let ident = match kind {
                            PatKind::Binding { var, .. } => ctx.rename(var.0),
                            _ => Ident::fresh_local(format!("_{ix}")),
                        };
                        (ident.into(), *span, *ty)
                    }
                    None => (Ident::fresh_local(format!("_{ix}")).into(), DUMMY_SP, param.ty),
                })
                .collect();
            let output = ctx.normalize_erasing_regions(
                rustc_middle::ty::TypingEnv::non_body_analysis(ctx.tcx, def_id),
                fn_sig.output(),
            );
            (inputs, output)
        }
        BodyTy::GlobalAsm(_) => {
            ctx.crash_and_error(ctx.def_span(def_id), "Inline assembly is not supported")
        }
    }
}

/// Normally this information is easier to extract from THIR (using `inputs_and_output_from_thir` above)
/// but sometimes there is no THIR available (e.g., trait method sigs). Closures also go through this for some reason.
pub fn inputs_and_output(tcx: TyCtxt, def_id: DefId) -> (Box<[(PIdent, Span, Ty)]>, Ty) {
    let ty = tcx.type_of(def_id).instantiate_identity();
    match ty.kind() {
        TyKind::FnDef(..) => {
            let gen_sig = tcx
                .instantiate_bound_regions_with_erased(tcx.fn_sig(def_id).instantiate_identity());
            let sig =
                tcx.normalize_erasing_regions(TypingEnv::non_body_analysis(tcx, def_id), gen_sig);
            let inputs = tcx
                .fn_arg_idents(def_id)
                .iter()
                .cloned()
                .zip(sig.inputs().iter().cloned())
                .enumerate()
                .map(|(ix, (ident, ty))| match ident {
                    Some(rustc_span::Ident { name, span }) => {
                        let name = name.as_str();
                        let ident = if name.is_empty() || name == "_" {
                            Ident::fresh_local(format!("_{ix}"))
                        } else {
                            Ident::fresh_local(variable_name(name))
                        };
                        (ident.into(), span, ty)
                    }
                    None => (Ident::fresh_local(format!("_{ix}")).into(), DUMMY_SP, ty),
                })
                .collect();
            (inputs, sig.output())
        }
        TyKind::Closure(_, subst) => {
            let sig = tcx.instantiate_bound_regions_with_erased(
                tcx.signature_unclosure(subst.as_closure().sig(), Safety::Safe),
            );
            let sig = tcx.normalize_erasing_regions(TypingEnv::non_body_analysis(tcx, def_id), sig);
            let env_ty = tcx.closure_env_ty(ty, subst.as_closure().kind(), tcx.lifetimes.re_erased);
            let closure_env = (name::self_().into(), tcx.def_span(def_id), env_ty);
            let names = tcx.fn_arg_idents(def_id).iter().cloned();
            let inputs = std::iter::once(closure_env)
                .chain(names.zip(sig.inputs().iter().cloned()).enumerate().map(
                    |(ix, (ident, ty))| match ident {
                        Some(rustc_span::Ident { name, span }) => {
                            let name = name.as_str();
                            let ident = if name.is_empty() || name == "_" {
                                Ident::fresh_local(format!("_{ix}"))
                            } else {
                                Ident::fresh_local(variable_name(name))
                            };
                            (ident.into(), span, ty)
                        }
                        None => (Ident::fresh_local(format!("_{ix}")).into(), DUMMY_SP, ty),
                    },
                ))
                .collect();
            (inputs, sig.output())
        }
        _ => ([].into(), tcx.type_of(def_id).instantiate_identity()),
    }
}
