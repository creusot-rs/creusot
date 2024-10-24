use crate::{
    contracts_items::{is_open_inv_result, is_pearlite},
    ctx::*,
    pearlite::TermVisitorMut,
    translation::{
        pearlite::{self, Term},
        specification::PreContract,
    },
    util::{anonymous_param_symbol, closure_capture_subst},
};
use rustc_hir::{def_id::DefId, Safety};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{
    self, ClosureKind, EarlyBinder, GenericArg, GenericArgs, Ty, TyCtxt, TyKind,
};
use rustc_span::{symbol, symbol::kw, Span, Symbol, DUMMY_SP};
use std::{
    collections::{HashMap, HashSet},
    iter,
};

#[derive(TypeVisitable, TypeFoldable, Debug, Clone)]
pub struct PreSignature<'tcx> {
    pub(crate) inputs: Vec<(symbol::Symbol, Span, Ty<'tcx>)>,
    pub(crate) output: Ty<'tcx>,
    pub(crate) contract: PreContract<'tcx>,
    // trusted: bool,
    // span: Span,
    // program: bool,
}

impl<'tcx> PreSignature<'tcx> {
    pub(crate) fn normalize(mut self, tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>) -> Self {
        self.contract = self.contract.normalize(tcx, param_env);
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
        let mut pre_subst = closure_capture_subst(ctx.tcx, def_id, subst, None, self_);

        let mut s = HashMap::new();
        let kind = subst.as_closure().kind();

        let env_ty = ctx.closure_env_ty(fn_ty, kind, ctx.lifetimes.re_erased);
        s.insert(
            self_,
            if env_ty.is_ref() { Term::var(self_, env_ty).cur() } else { Term::var(self_, env_ty) },
        );
        for pre in &mut contract.requires {
            pre_subst.visit_mut_term(pre);

            pre.subst(&s);
        }

        if kind == ClosureKind::FnMut {
            let args = subst.as_closure().sig().inputs().skip_binder()[0];
            let unnest_subst =
                ctx.mk_args(&[GenericArg::from(args), GenericArg::from(env_ty.peel_refs())]);

            let unnest_id = ctx.get_diagnostic_item(Symbol::intern("fn_mut_impl_unnest")).unwrap();

            contract.ensures.push(Term::call(
                ctx.tcx,
                unnest_id,
                unnest_subst,
                vec![Term::var(self_, env_ty).cur(), Term::var(self_, env_ty).fin()],
            ));
        };

        let mut post_subst =
            closure_capture_subst(ctx.tcx, def_id, subst, Some(subst.as_closure().kind()), self_);
        for post in &mut contract.ensures {
            post_subst.visit_mut_term(post);
        }

        assert!(contract.variant.is_none());
    }

    let mut inputs: Vec<_> = inputs
        .enumerate()
        .map(|(idx, (ident, ty))| {
            if ident.name.as_str() == "result" {
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

    let mut pre_sig = PreSignature { inputs, output, contract };
    elaborate_type_invariants(ctx, def_id, &mut pre_sig);
    pre_sig
}

fn elaborate_type_invariants<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    pre_sig: &mut PreSignature<'tcx>,
) {
    if is_pearlite(ctx.tcx, def_id) {
        return;
    }

    let subst = GenericArgs::identity_for_item(ctx.tcx, def_id);

    let params_open_inv: HashSet<usize> = ctx
        .params_open_inv(def_id)
        .iter()
        .copied()
        .flatten()
        .map(|&i| if ctx.tcx.is_closure_like(def_id) { i + 1 } else { i })
        .collect();
    for (i, (name, span, ty)) in pre_sig.inputs.iter().enumerate() {
        if params_open_inv.contains(&i) {
            continue;
        }
        if let Some(term) = pearlite::type_invariant_term(ctx, def_id, *name, *span, *ty) {
            let term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
            pre_sig.contract.requires.push(term);
        }
    }

    let ret_ty_span: Option<Span> = try { ctx.tcx.hir().get_fn_output(def_id.as_local()?)?.span() };
    if !is_open_inv_result(ctx.tcx, def_id)
        && let Some(term) = pearlite::type_invariant_term(
            ctx,
            def_id,
            Symbol::intern("result"),
            ret_ty_span.unwrap_or_else(|| ctx.tcx.def_span(def_id)),
            pre_sig.output,
        )
    {
        let term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
        pre_sig.contract.ensures.push(term);
    }
}

pub(crate) fn inputs_and_output<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (impl Iterator<Item = (symbol::Ident, Ty<'tcx>)>, Ty<'tcx>) {
    let ty = tcx.type_of(def_id).instantiate_identity();
    let (inputs, output): (Box<dyn Iterator<Item = (rustc_span::symbol::Ident, _)>>, _) = match ty
        .kind()
    {
        TyKind::FnDef(..) => {
            let gen_sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = tcx.normalize_erasing_late_bound_regions(tcx.param_env(def_id), gen_sig);
            let iter = tcx.fn_arg_names(def_id).iter().cloned().zip(sig.inputs().iter().cloned());
            (Box::new(iter), sig.output())
        }
        TyKind::Closure(_, subst) => {
            let sig = tcx.signature_unclosure(subst.as_closure().sig(), Safety::Safe);
            let sig = tcx.normalize_erasing_late_bound_regions(tcx.param_env(def_id), sig);
            let env_ty = tcx.closure_env_ty(ty, subst.as_closure().kind(), tcx.lifetimes.re_erased);

            // I wish this could be called "self"
            let closure_env = (symbol::Ident::empty(), env_ty);
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
