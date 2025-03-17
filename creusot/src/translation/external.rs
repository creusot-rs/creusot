use crate::{
    ctx::*,
    error::CreusotResult,
    translation::{
        pearlite::Term,
        specification::{ContractClauses, contract_clauses_of},
        traits::TraitResolved,
    },
    util::erased_identity_for_item,
};
use indexmap::IndexSet;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    thir::{self, Expr, ExprKind, Thir, visit::Visitor},
    ty::{Clause, EarlyBinder, GenericArgKind, GenericArgsRef, Predicate, TyCtxt, TyKind},
};
use rustc_span::Symbol;
use rustc_type_ir::ConstKind;

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub(crate) struct ExternSpec<'tcx> {
    // The contract we are attaching
    pub contract: ContractClauses,
    pub subst: GenericArgsRef<'tcx>,
    pub arg_subst: Vec<(Symbol, Term<'tcx>)>,
    // Additional predicates we must verify to call this function
    pub additional_predicates: Vec<Predicate<'tcx>>,
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
pub(crate) fn extract_extern_specs_from_item<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: LocalDefId,
) -> CreusotResult<(DefId, ExternSpec<'tcx>)> {
    // Handle error gracefully
    let (thir, expr) = ctx.fetch_thir(def_id)?;
    let thir = thir.borrow();

    let mut visit = ExtractExternItems::new(&thir);

    visit.visit_expr(&thir[expr]);

    let (id, subst) = visit.items.pop().unwrap();

    let (id, _) = if ctx.trait_of_item(id).is_some() {
        TraitResolved::resolve_item(ctx.tcx, ctx.typing_env(def_id.to_def_id()), id, subst).to_opt(id, subst).unwrap_or_else(|| {
            let mut err = ctx.fatal_error(
                ctx.def_span(def_id.to_def_id()),
                "could not derive original instance from external specification",
            );

            err.span_warn(ctx.def_span(def_id.to_def_id()), "the bounds on an external specification must be at least as strong as the original impl bounds");
            err.emit()
        })
    } else {
        (id, subst)
    };

    // Generics of the actual item.
    let mut inner_subst = erased_identity_for_item(ctx.tcx, id).to_vec();
    // Generics of our stub.
    let outer_subst = erased_identity_for_item(ctx.tcx, def_id.to_def_id());

    // FIXME(xavier): I don't remember the original reason for introducing this...
    let extra_parameters = inner_subst.len() - outer_subst.len();

    // Move Self_ to the front of the list like rustc does for real trait impls (not expressible in surface rust).
    // This only matters when we also have lifetime parameters.
    let self_pos = outer_subst.iter().position(|e| {
        if let GenericArgKind::Type(t) = e.unpack()
            && let TyKind::Param(t) = t.kind()
            && t.name.as_str().starts_with("Self")
        {
            true
        } else {
            false
        }
    });

    if let Some(ix) = self_pos {
        let self_ = inner_subst.remove(ix + extra_parameters);
        inner_subst.insert(extra_parameters, self_);
    };

    let mut subst = Vec::new();
    let mut errors = Vec::new();
    for i in 0..outer_subst.len() {
        let span = ctx.def_span(def_id.to_def_id());
        match (inner_subst[i + extra_parameters].unpack(), outer_subst[i].unpack()) {
            (GenericArgKind::Type(t1), GenericArgKind::Type(t2)) => match (t1.kind(), t2.kind()) {
                (TyKind::Param(param1), TyKind::Param(param2))
                    if param1.name == param2.name || param1.name.as_str().starts_with("Self") =>
                {
                    subst.push(inner_subst[i + extra_parameters]);
                }
                _ => {
                    let mut err = ctx.fatal_error(span, "mismatched parameters in `extern_spec!`");
                    err.warn(format!("expected parameter `{:?}` to be called `{:?}`", t2, t1));
                    errors.push(err);
                }
            },
            (GenericArgKind::Const(c1), GenericArgKind::Const(c2)) => {
                let is_eq = match (c1.kind(), c2.kind()) {
                    (ConstKind::Param(param1), ConstKind::Param(param2)) => {
                        param1.name == param2.name
                    }
                    // TODO: also compare the name only in these other cases (if this is not already the case)
                    (_, _) => c1 == c2,
                };
                if is_eq {
                    subst.push(inner_subst[i + extra_parameters]);
                } else {
                    let mut err = ctx.fatal_error(span, "mismatched parameters in `extern_spec!`");
                    err.warn(format!("expected parameter `{:?}` to be called `{:?}`", c2, c1));
                    errors.push(err);
                }
            }
            (GenericArgKind::Lifetime(l1), GenericArgKind::Lifetime(l2)) => {
                if l1.get_name() == l2.get_name() {
                    subst.push(inner_subst[i + extra_parameters]);
                } else {
                    let mut err = ctx.fatal_error(span, "mismatched parameters in `extern_spec!`");
                    err.warn(format!("expected parameter `{:?}` to be called `{:?}`", l2, l1));
                    errors.push(err);
                }
            }
            _ => {
                let err = ctx.fatal_error(span, "mismatched parameters kind in `extern_spec!`");
                errors.push(err);
            }
        }
    }

    errors.into_iter().for_each(|e| e.emit());

    let subst = ctx.mk_args(&subst);

    let contract = contract_clauses_of(ctx, def_id.to_def_id()).unwrap();

    let additional_predicates = ctx
        .predicates_of(def_id)
        .instantiate(ctx.tcx, subst)
        .predicates
        .into_iter()
        .map(Clause::as_predicate)
        .collect();

    let arg_subst = ctx
        .fn_arg_names(def_id)
        .iter()
        .zip(ctx.fn_arg_names(id).iter().zip(ctx.fn_sig(id).instantiate_identity().inputs().iter()))
        .map(|(i, (i2, ty))| {
            let ty = ctx.tcx.instantiate_bound_regions_with_erased(ty.map_bound(|&ty| ty));
            (i.name, Term::var(i2.name, ty))
        })
        .collect();
    Ok((id, ExternSpec { contract, additional_predicates, subst, arg_subst }))
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
