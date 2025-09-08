use super::specification::inputs_and_output_from_thir;
use crate::{
    ctx::*,
    translation::{
        pearlite::PIdent,
        specification::{ContractClauses, contract_clauses_of},
        traits::TraitResolved,
    },
    util::erased_identity_for_item,
    validate::is_ghost_ty_,
};
use indexmap::IndexSet;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    thir::{self, Expr, ExprKind, Thir, visit::Visitor},
    ty::{Clause, EarlyBinder, GenericArgKind, GenericArgsRef, Predicate, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
use rustc_type_ir::ConstKind;

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub(crate) struct ExternSpec<'tcx> {
    // The contract we are attaching
    pub(crate) contract: ContractClauses,
    pub(crate) subst: GenericArgsRef<'tcx>,
    pub(crate) inputs: Box<[(PIdent, Span, Ty<'tcx>)]>,
    pub(crate) output: Ty<'tcx>,
    // Additional predicates we must verify to call this function
    pub(crate) additional_predicates: Vec<Predicate<'tcx>>,
}

impl<'tcx> ExternSpec<'tcx> {
    pub(crate) fn predicates_for(
        &self,
        tcx: TyCtxt<'tcx>,
        sub: GenericArgsRef<'tcx>,
    ) -> Vec<Predicate<'tcx>> {
        EarlyBinder::bind(self.additional_predicates.clone()).instantiate(tcx, sub)
    }
}

// Must be run before MIR generation.
//
// An extern spec desugars to a wrapper function:
//
// ```
// extern_spec! {
//   #[requires(p(x))]
//   fn f<T>(x: T) -> U;
// }
// ```
//
// becomes, approximately:
//
// ```
// #[requires(p(x))]
// fn extern_spec_f<T>(x: T) -> U {
//   f::<T>(x)
// }
// ```
//
// `local_def_id` is the `LocalDefId` of `extern_spec_f`.
pub(crate) fn extract_extern_specs_from_item<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    local_def_id: LocalDefId,
    &(ref thir, expr): &(Thir<'tcx>, thir::ExprId),
) -> (DefId, ExternSpec<'tcx>) {
    let def_id = local_def_id.to_def_id();
    let span = ctx.def_span(def_id);
    let contract = contract_clauses_of(ctx, def_id).unwrap();
    let mut visit = ExtractExternItems::new(thir);
    visit.visit_expr(&thir[expr]);
    let (id, subst) = visit.items.pop().unwrap();

    let (id, inner_subst) =
        TraitResolved::resolve_item(ctx.tcx, ctx.typing_env(def_id), id, subst).to_opt(id, subst).unwrap_or_else(|| {
            let mut err = ctx.fatal_error(
                ctx.def_span(def_id),
                "could not derive original instance from external specification",
            );

            err.span_warn(ctx.def_span(def_id), "the bounds on an external specification must be at least as strong as the original impl bounds");
            err.emit()
        });

    // The following computes a substitution `subst` that we can apply to the contract of
    // `extern_spec_f` given some type arguments for `f`:
    // 1. check that `inner_generics` is a permutation of `outer_subst`;
    // 2. invert it.
    // Generics of our stub.
    let outer_subst = erased_identity_for_item(ctx.tcx, def_id);
    // Generics of the actual item.
    let inner_generics = erased_identity_for_item(ctx.tcx, id).to_vec();
    let mut subst = vec![None; inner_generics.len()];
    let crash = || -> ! {
        ctx.crash_and_error(
            span,
            format!(
                "extern spec generics don't match\n {} {:?}\n {} {:?}",
                ctx.def_path_str(def_id),
                outer_subst,
                ctx.def_path_str(id),
                inner_subst
            ),
        )
    };
    // Traverse `inner_subst` (= the type arguments of `f` in the body of `extern_spec_f`),
    // check that they are all variables, that each variable is mentioned exactly once, and invert the substitution.
    // Lifetimes are ignored and erased.
    for (param, arg) in inner_generics.into_iter().zip(inner_subst) {
        match arg.kind() {
            GenericArgKind::Type(ty) => match ty.kind() {
                TyKind::Param(p) => match subst[p.index as usize] {
                    ref mut q @ None => *q = Some(param),
                    Some(_) => crash(),
                },
                _ => crash(),
            },
            GenericArgKind::Const(c) => match c.kind() {
                ConstKind::Param(p) => match subst[p.index as usize] {
                    ref mut q @ None => *q = Some(param),
                    Some(_) => crash(),
                },
                _ => crash(),
            },
            GenericArgKind::Lifetime(_) => {}
        }
    }
    let subst = subst
        .into_iter()
        .zip(outer_subst)
        .map(|(o, p)| {
            o.unwrap_or_else(|| match p.kind() {
                GenericArgKind::Lifetime(_) => p,
                _ => crash(),
            })
        })
        .collect::<Box<[_]>>();
    let subst = ctx.mk_args(&subst);

    let additional_predicates = ctx
        .predicates_of(local_def_id)
        .instantiate(ctx.tcx, subst)
        .predicates
        .into_iter()
        .map(Clause::as_predicate)
        .collect();

    let (inputs, output) = inputs_and_output_from_thir(ctx, def_id, thir);
    (id, ExternSpec { contract, additional_predicates, subst, inputs, output })
}

// We shouldn't need a full visitor... or an index set, there should be a single item per extern spec method.
struct ExtractExternItems<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    pub items: IndexSet<(DefId, GenericArgsRef<'tcx>)>,
}

impl<'a, 'tcx> ExtractExternItems<'a, 'tcx> {
    pub(crate) fn new(thir: &'a Thir<'tcx>) -> Self {
        ExtractExternItems { thir, items: IndexSet::new() }
    }
}

impl<'a, 'tcx> thir::visit::Visitor<'a, 'tcx> for ExtractExternItems<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a Expr<'tcx>) {
        if let ExprKind::Call { ty, .. } = expr.kind {
            if let TyKind::FnDef(id, subst) = ty.kind() {
                self.items.insert((*id, subst));
            }
        }
        thir::visit::walk_expr(self, expr);
    }
}

// There's probably a better place for the following.
// It is here because it is similar logic to `extract_extern_specs_from_item` above.

/// Input: `local_def_id` of a `#[creusot::spec::erasure]` closure.
/// Output:
/// - `LocalDefId` of the original `#[erasure]` item (the parent of the input id)
/// - `Erased<'tcx>` info about the erased function from the point of view of callers
///   (THIR trait method calls are not resolved)
/// - `(DefId, GenericArgsRef)` of the actual body of the erased function
pub(crate) fn extract_erasure_from_item<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    local_def_id: LocalDefId,
    &(ref thir, expr): &(Thir<'tcx>, thir::ExprId),
) -> (LocalDefId, Erased<'tcx>, (DefId, GenericArgsRef<'tcx>)) {
    let def_id = local_def_id.to_def_id();
    let parent = ctx.tcx.parent(def_id);
    let span = ctx.def_span(def_id);
    let mut visit = ExtractExternItems::new(thir);
    visit.visit_expr(&thir[expr]);
    let (id_thir, subst_thir) = visit.items.pop().unwrap();
    let (id_resolved, subst_resolved) =
        TraitResolved::resolve_item(ctx.tcx, ctx.typing_env(def_id), id_thir, subst_thir).to_opt(id_thir, subst_thir).unwrap_or_else(|| {
            let mut err = ctx.fatal_error(
                ctx.def_span(def_id),
                "could not derive original instance from external specification",
            );
            err.span_warn(ctx.def_span(def_id), "the bounds on an external specification must be at least as strong as the original impl bounds");
            err.emit()
        });
    let parent_sig = ctx
        .tcx
        .instantiate_bound_regions_with_erased(ctx.tcx.fn_sig(parent).instantiate_identity());
    // Check that the result types match
    let ty1 = parent_sig.output();
    let ty2 = thir[expr].ty;
    if !eq_erased_ty(ctx.tcx, ty1, ty2) {
        ctx.crash_and_error(
            span,
            format!(
                "result type of target function doesn't match\n {}(..) -> {}\n {}(..) -> {}",
                ctx.def_path_str(parent),
                ty1,
                ctx.def_path_str(id_resolved),
                ty2,
            ),
        )
    }
    let erase_args = parent_sig.inputs().iter().map(|arg| is_ghost_ty_(ctx.tcx, *arg)).collect();
    (
        parent.expect_local(),
        Erased { def: (id_thir, subst_thir), erase_args },
        (id_resolved, subst_resolved),
    )
}

/// `ty1` equals `ty2` up to erasure if:
/// - `ty1 == ty2`
/// - `ty2 == (ty3, Ghost<_>)` and `ty1` equals `ty2` up to erasure
/// - `*mut T` and `*const T` are also equal up to erasure
fn eq_erased_ty<'tcx>(tcx: TyCtxt<'tcx>, ty1: Ty<'tcx>, ty2: Ty<'tcx>) -> bool {
    if ty1 == ty2 {
        return true;
    }
    match ty1.kind() {
        TyKind::Tuple(tys)
            if tys.len() == 2 && eq_erased_ty(tcx, tys[0], ty2) && is_ghost_ty_(tcx, tys[1]) =>
        {
            true
        }
        TyKind::RawPtr(ty1, _) if let TyKind::RawPtr(ty2, _) = ty2.kind() => ty1 == ty2,
        _ => false,
    }
}
