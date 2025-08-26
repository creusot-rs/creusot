use super::specification::inputs_and_output_from_thir;
use crate::{
    ctx::*,
    translation::{
        pearlite::PIdent,
        specification::{ContractClauses, contract_clauses_of},
        traits,
    },
    util::erased_identity_for_item,
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

    let (id, _) =
        traits::resolve_item(ctx.tcx, ctx.typing_env(def_id), id, subst).found().unwrap_or_else(|| {
            let mut err = ctx.fatal_error(
                span,
                "could not derive original instance from external specification",
            );
            err.span_warn(span, "the bounds on an external specification must be at least as strong as the original impl bounds");
            err.emit()
        });

    // Generics of the actual item.
    let mut inner_subst = erased_identity_for_item(ctx.tcx, id).to_vec();
    // Generics of our stub.
    let outer_subst = erased_identity_for_item(ctx.tcx, def_id);

    // FIXME: I don't remember the original reason for introducing this...
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

    // since `outer_subst` has all its generic coming from a function (no `impl`),
    // it always puts lifetimes first.
    inner_subst.sort_by(|a1, a2| {
        use std::cmp::Ordering;
        match (a1.unpack(), a2.unpack()) {
            (GenericArgKind::Lifetime(_), GenericArgKind::Lifetime(_)) => Ordering::Equal,
            (GenericArgKind::Lifetime(_), _) => Ordering::Less,
            (_, GenericArgKind::Lifetime(_)) => Ordering::Greater,
            _ => Ordering::Equal,
        }
    });

    let mut subst = Vec::new();
    let mut errors = Vec::new();
    for i in 0..outer_subst.len() {
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
            (arg_expected, arg) => {
                let p_str = |arg| match arg {
                    GenericArgKind::Lifetime(l) => format!("lifetime `{l:?}`"),
                    GenericArgKind::Type(t) => format!("type `{t:?}`"),
                    GenericArgKind::Const(c) => format!("constant `{c:?}`"),
                };
                let err = ctx.dcx().struct_span_fatal(
                    span,
                    format!(
                        "mismatched parameter kinds in `extern_spec!`: expected {}, got {}",
                        p_str(arg_expected),
                        p_str(arg)
                    ),
                );
                errors.push(err);
            }
        }
    }

    errors.into_iter().for_each(|e| e.emit());

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
