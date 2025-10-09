use super::specification::inputs_and_output_from_thir;
use crate::{
    contracts_items::{ErasureKind, get_erasure, is_trusted},
    ctx::*,
    translation::{
        pearlite::PIdent,
        specification::{ContractClauses, contract_clauses_of},
        traits::TraitResolved,
    },
    util::{eq_nameless_generic_args, erased_identity_for_item, forge_def_id, forge_def_id_from},
    validate::is_ghost_or_snap,
};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    thir::{self, Expr, ExprKind, Thir, visit::Visitor},
    ty::{
        Clause, EarlyBinder, GenericArgKind, GenericArgsRef, Predicate, Ty, TyCtxt, TyKind,
        TypingEnv,
    },
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
    (thir, expr): ThirExpr<'tcx>,
) -> (DefId, ExternSpec<'tcx>) {
    let def_id = local_def_id.to_def_id();
    let thir = &thir.borrow();
    let span = ctx.def_span(def_id);
    let contract = contract_clauses_of(ctx, def_id).unwrap();
    let (id, subst) = extract_extern_item(thir, expr).unwrap();
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

/// Extract a target item for `extern_spec!` or `#[erasure]`.
/// The visited body should be just a function call.
fn extract_extern_item<'tcx>(
    thir: &Thir<'tcx>,
    expr_id: thir::ExprId,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let mut visitor = ExtractExternItem::new(thir);
    visitor.visit_expr(&thir[expr_id]);
    visitor.item
}

struct ExtractExternItem<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    item: Option<(DefId, GenericArgsRef<'tcx>)>,
}

impl<'a, 'tcx> ExtractExternItem<'a, 'tcx> {
    pub fn new(thir: &'a Thir<'tcx>) -> Self {
        ExtractExternItem { thir, item: None }
    }
}

impl<'a, 'tcx> thir::visit::Visitor<'a, 'tcx> for ExtractExternItem<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a Expr<'tcx>) {
        if let ExprKind::Call { ty, .. } = expr.kind {
            if let TyKind::FnDef(id, subst) = ty.kind() {
                self.item = Some((*id, subst));
            }
        } else {
            thir::visit::walk_expr(self, expr);
        }
    }
}

// There's probably a better place for the following.
// It is here because it is similar logic to `extract_extern_specs_from_item` above.

/// Input: `local_def_id` of a `#[creusot::spec::erasure]` closure.
/// Output:
/// - `LocalDefId` of the original `#[erasure]` item (the parent of the input id)
/// - `Option<Erasure<'tcx>>` info about the erased function from the point of view of callers
///   (THIR trait method calls are not resolved), or `None` for ghost .
/// - `Option<Erasure<'tcx>>` of the actual body of the erased function, if
///   the `#[erasure]`-carrying function is not also `#[trusted]`.
pub(crate) fn extract_erasure_from_item<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    local_def_id: LocalDefId,
    (thir, expr): ThirExpr<'tcx>,
) -> Option<(LocalDefId, Option<Erasure<'tcx>>, Option<Erasure<'tcx>>)> {
    let def_id = local_def_id.to_def_id();
    let (id_this, (id_erased, subst_erased), (id_resolved, subst_resolved)) =
        match get_erasure(ctx.tcx, def_id) {
            None => return None,
            Some(ErasureKind::Parent) => {
                let parent = ctx.tcx.parent(def_id);
                let (id_erased, subst_erased) = extract_extern_item(&thir.borrow(), expr).unwrap();
                debug!("extract_erasure_from_item: {parent:?} erases to {id_erased:?}");
                let (id_resolved, subst_resolved) = TraitResolved::resolve_item(
                    ctx.tcx,
                    ctx.typing_env(def_id),
                    id_erased,
                    subst_erased,
                )
                .to_opt(id_erased, subst_erased)
                .unwrap_or_else(|| {
                    ctx.crash_and_error(
                        ctx.def_span(def_id),
                        "could not resolve `#[erasure]` target",
                    )
                });
                (parent, (id_erased, subst_erased), (id_resolved, subst_resolved))
            }
            Some(ErasureKind::Private(path)) => {
                debug!("extract_erasure_from_item: {def_id:?} erases to private {path:?}");
                let id_erased = forge_def_id(ctx.tcx, &path)
                    .unwrap_or_else(|e| ctx.crash_and_error(ctx.def_span(def_id), e));
                let subst_erased = erased_identity_for_item(ctx.tcx, id_erased);
                let subst_this = erased_identity_for_item(ctx.tcx, def_id);
                if !eq_nameless_generic_args(subst_erased, subst_this) {
                    ctx.crash_and_error(
                        ctx.def_span(def_id),
                        format!(
                            "#[erasure] generics don't match\n {} {:?}\n {} {:?}",
                            ctx.def_path_str(def_id),
                            subst_this,
                            ctx.def_path_str(id_erased),
                            subst_erased,
                        ),
                    )
                }
                (def_id, (id_erased, subst_erased), (id_erased, subst_erased))
            }
            Some(ErasureKind::Ghost) => {
                if !is_trusted(ctx.tcx, def_id) {
                    ctx.crash_and_error(
                        ctx.def_span(def_id),
                        format!("#[erasure(_)] requires the #[trusted] attribute"),
                    )
                }
                return Some((local_def_id, None, None));
            }
        };
    let erased = build_erased(ctx.tcx, ctx.typing_env(id_this), id_this, id_erased, subst_erased);
    let to_check = if is_trusted(ctx.tcx, id_this) {
        None
    } else {
        Some(Erasure { def: (id_resolved, subst_resolved), erase_args: erased.erase_args.clone() })
    };
    Some((id_this.expect_local(), Some(erased), to_check))
}

/// Extract erasure for nested items
pub(crate) fn extract_erasure_from_child<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    local_def_id: LocalDefId,
) -> Option<Erasure<'tcx>> {
    let def_id = local_def_id.to_def_id();
    if !matches!(ctx.tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
        || ctx.erasure(def_id).is_some()
    {
        return None;
    }
    let mut parent = def_id;
    let mut rev_path = Vec::new();
    let erased_parent = loop {
        let def_key = ctx.tcx.def_key(parent);
        let Some(parent_id) = def_key.parent else { return None };
        rev_path.push(def_key.disambiguated_data);
        parent.index = parent_id;
        if is_trusted(ctx.tcx, parent) {
            return None;
        };
        match ctx.erasure_to_check(LocalDefId { local_def_index: parent.index }) {
            Some(erased) => break erased,
            None => {
                continue;
            }
        }
    };
    debug!("extract_erasure_from_child: child: {local_def_id:?} parent: {:?}", erased_parent.def.0);
    let hash = ctx.def_path_hash(erased_parent.def.0);
    let path = rev_path.into_iter().rev();
    let Some(erased) = forge_def_id_from(ctx.tcx, hash, path) else {
        ctx.tcx
            .error(ctx.def_span(def_id), "erasure not found")
            .with_span_label(ctx.def_span(parent), "required by #[erasure] on this function")
            .emit();
        return None;
    };
    let subst = erased_identity_for_item(ctx.tcx, def_id);
    let erased_subst = erased_identity_for_item(ctx.tcx, erased);
    if !eq_nameless_generic_args(subst, erased_subst) {
        ctx.crash_and_error(
            ctx.def_span(def_id),
            format!(
                "#[erasure] generics don't match\n {} {:?}\n {} {:?}",
                ctx.def_path_str(def_id),
                subst,
                ctx.def_path_str(erased),
                erased_subst
            ),
        )
    }
    build_erased(ctx.tcx, ctx.typing_env(def_id), def_id, erased, erased_subst).into()
}

fn build_erased<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id1: DefId,
    def_id2: DefId,
    subst2: GenericArgsRef<'tcx>,
) -> Erasure<'tcx> {
    let sig1 =
        tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(def_id1).instantiate_identity());
    let sig2 = tcx.instantiate_bound_regions_with_erased(
        tcx.instantiate_and_normalize_erasing_regions(subst2, typing_env, tcx.fn_sig(def_id2)),
    );
    let ty1 = sig1.output();
    let ty2 = sig2.output();
    if !eq_erased_ty(tcx, ty1, ty2) {
        tcx.crash_and_error(
            tcx.def_span(def_id1),
            format!(
                "#[erasure] check failed: result types don't match\n {}(..) -> {:?}\n {}(..) -> {:?}",
                tcx.def_path_str(def_id1),
                ty1,
                tcx.def_path_str(def_id2),
                ty2,
            ),
        )
    }
    let erase_args =
        sig1.inputs().iter().map(|arg| is_ghost_or_snap(tcx, *arg)).collect::<Vec<bool>>();
    let len_unerased_args = erase_args.iter().filter(|&&erase| !erase).count();
    let unerased_args1 = sig1
        .inputs()
        .iter()
        .zip(erase_args.iter())
        .filter_map(|(ty, &erase)| if erase { None } else { Some(ty) });
    if len_unerased_args != sig2.inputs().len()
        || !unerased_args1.zip(sig2.inputs()).all(|(ty1, ty2)| eq_erased_ty(tcx, *ty1, *ty2))
    {
        tcx.crash_and_error(
            tcx.def_span(def_id1),
            format!(
                "#[erasure] check failed: argument types don't match\n {}({:?}) -> ...\n {}({:?}) -> ...",
                tcx.def_path_str(def_id1),
                sig1.inputs(),
                tcx.def_path_str(def_id2),
                sig2.inputs()
            ),
        )
    }
    Erasure { def: (def_id2, subst2), erase_args }
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
            if tys.len() == 2
                && eq_erased_ty(tcx, tys[0], ty2)
                && is_ghost_or_snap(tcx, tys[1]) =>
        {
            true
        }
        TyKind::RawPtr(ty1, _) if let TyKind::RawPtr(ty2, _) = ty2.kind() => ty1 == ty2,
        _ => false,
    }
}
