use crate::{
    ctx::*,
    error::{CrErr, CreusotResult},
    function::all_generic_decls_for,
    translation::{traits, translate_logic_or_predicate},
    util::item_type,
};
use creusot_rustc::{
    hir::def_id::{DefId, LocalDefId},
    macros::{TyDecodable, TyEncodable},
    middle::{
        thir::{self, visit::Visitor, Expr, ExprKind, Thir},
        ty::{
            subst::{GenericArgKind, InternalSubsts, Subst, SubstsRef},
            EarlyBinder, Predicate, TyCtxt, TyKind, WithOptConstParam,
        },
    },
    span::{Symbol, DUMMY_SP},
};
use indexmap::IndexSet;
use why3::declaration::{Decl, Module, ValKind, ValKind::Val};

use super::specification::{
    typing::{Term, TermKind},
    ContractClauses,
};

pub(crate) fn default_decl<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Module, CloneSummary<'tcx>) {
    info!("generating default declaration for def_id={:?}", def_id);
    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Interface);

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));

    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    let name = module_name(ctx, def_id);

    decls.extend(names.to_clones(ctx));
    let decl = match item_type(ctx.tcx, def_id) {
        ItemType::Logic => ValKind::Function { sig },
        ItemType::Predicate => {
            sig.retty = None;
            ValKind::Predicate { sig }
        }
        ItemType::Program => {
            if !ctx.externs.verified(def_id) && sig.contract.is_empty() {
                sig.contract.requires.push(why3::exp::Exp::mk_false());
            }
            Val { sig }
        }
        _ => unreachable!("default_decl: Expected function"),
    };
    decls.push(Decl::ValDecl(decl));

    (Module { name, decls }, names.summary())
}

pub(crate) fn extern_module<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (
    Module,
    Option<CloneSummary<'tcx>>, // None is used to refer to dependencies that should be fetched from metadata
) {
    match ctx.externs.term(def_id) {
        Some(_) => {
            match item_type(ctx.tcx, def_id) {
                // the dependencies should be what was already stored in the metadata...
                ItemType::Logic | ItemType::Predicate => {
                    (translate_logic_or_predicate(ctx, def_id).0, None)
                }
                _ => unreachable!("extern_module: unexpected term for {:?}", def_id),
            }
        }
        None => {
            let (modl, deps) = default_decl(ctx, def_id);
            // Why do we ever want to return `Err` shouldn't `deps` already be correct?
            let deps = if ctx.externs.dependencies(def_id).is_some() { None } else { Some(deps) };
            (modl, deps)
        }
    }
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub(crate) struct ExternSpec<'tcx> {
    // The contract we are attaching
    pub contract: ContractClauses,
    pub subst: SubstsRef<'tcx>,
    pub arg_subst: Vec<(Symbol, Term<'tcx>)>,
    // Additional predicates we must verify to call this function
    pub additional_predicates: Vec<Predicate<'tcx>>,
}

impl<'tcx> ExternSpec<'tcx> {
    pub(crate) fn predicates_for(
        &self,
        tcx: TyCtxt<'tcx>,
        sub: SubstsRef<'tcx>,
    ) -> Vec<Predicate<'tcx>> {
        EarlyBinder(self.additional_predicates.clone()).subst(tcx, sub)
    }
}

// Must be run before MIR generation.
pub(crate) fn extract_extern_specs_from_item<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: LocalDefId,
) -> CreusotResult<(DefId, ExternSpec<'tcx>)> {
    // Handle error gracefully
    let (thir, expr) = ctx.tcx.thir_body(WithOptConstParam::unknown(def_id)).map_err(|_| CrErr)?;
    let thir = thir.borrow();

    let mut visit = ExtractExternItems::new(&thir);

    visit.visit_expr(&thir[expr]);

    let (id, subst) = visit.items.pop().unwrap();

    let (id, _) = if ctx.trait_of_item(id).is_some() {
        let resolved = traits::resolve_opt(ctx.tcx, ctx.param_env(def_id.to_def_id()), id, subst);

        if let None = resolved {
            let mut err = ctx.fatal_error(
                ctx.def_span(def_id.to_def_id()),
                "could not derive original instance from external specification",
            );

            err.span_warn(ctx.def_span(def_id.to_def_id()), "the bounds on an external specification must be at least as strong as the original impl bounds");
            err.emit()
        };
        resolved.unwrap()
    } else {
        (id, subst)
    };

    let inner_subst = InternalSubsts::identity_for_item(ctx.tcx, id);
    let outer_subst = InternalSubsts::identity_for_item(ctx.tcx, def_id.to_def_id());

    let extra_parameters = inner_subst.len() - outer_subst.len();

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
                    err.warn(&format!("expected parameter `{:?}` to be called `{:?}`", t2, t1));
                    errors.push(err);
                }
            },
            (GenericArgKind::Const(c1), GenericArgKind::Const(c2)) => {
                if c1 == c2 {
                    subst.push(inner_subst[i + extra_parameters]);
                } else {
                    let mut err = ctx.fatal_error(span, "mismatched parameters in `extern_spec!`");
                    err.warn(&format!("expected parameter `{:?}` to be called `{:?}`", c2, c1));
                    errors.push(err);
                }
            }
            _ => {}
        }
    }

    errors.into_iter().for_each(|mut e| e.emit());

    let subst = ctx.mk_substs(subst.into_iter());

    let contract = crate::specification::contract_clauses_of(ctx, def_id.to_def_id()).unwrap();

    let additional_predicates =
        ctx.tcx.predicates_of(def_id).instantiate(ctx.tcx, subst).predicates.into_iter().collect();

    let arg_subst = ctx
        .tcx
        .fn_arg_names(def_id)
        .iter()
        .zip(ctx.tcx.fn_arg_names(id).iter().zip(ctx.fn_sig(id).skip_binder().inputs()))
        .map(|(i, (i2, ty))| {
            (i.name, Term { ty: *ty, kind: TermKind::Var(i2.name), span: DUMMY_SP })
        })
        .collect();
    Ok((id, ExternSpec { contract, additional_predicates, subst, arg_subst }))
}

// We shouldn't need a full visitor... or an index set, there should be a single item per extern spec method.
struct ExtractExternItems<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    pub items: IndexSet<(DefId, SubstsRef<'tcx>)>,
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

    fn visit_expr(&mut self, expr: &Expr<'tcx>) {
        if let ExprKind::Call { ty, .. } = expr.kind {
            if let TyKind::FnDef(id, subst) = ty.kind() {
                self.items.insert((*id, subst));
            }
        }
        thir::visit::walk_expr(self, expr);
    }
}
