use crate::function::all_generic_decls_for;
use crate::translation;
use crate::util::item_type;
use crate::{ctx::*, util};
use indexmap::IndexSet;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::thir::visit::Visitor;
use rustc_middle::thir::{self, Expr, ExprKind, Thir};
use rustc_middle::ty::subst::{InternalSubsts, Subst, SubstsRef};
use rustc_middle::ty::{Predicate, TyCtxt, TyKind, WithOptConstParam};
use why3::declaration::ValKind;
use why3::declaration::{Decl, Module, ValKind::Val};

use super::specification::PreContract;

pub fn default_decl(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Module, CloneSummary<'tcx>) {
    info!("generating default declaration for def_id={:?}", def_id);
    let mut names =
        CloneMap::new(ctx.tcx, def_id, !util::item_type(ctx.tcx, def_id).is_transparent());

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));

    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    let name = module_name(ctx.tcx, def_id);

    decls.extend(names.to_clones(ctx));
    let decl = match item_type(ctx.tcx, def_id) {
        ItemType::Logic => ValKind::Function { sig },
        ItemType::Predicate => {
            sig.retty = None;
            ValKind::Predicate { sig }
        }
        ItemType::Program => {
            if !ctx.externs.verified(def_id) && ctx.extern_spec(def_id).is_none() {
                sig.contract.requires.push(why3::mlcfg::Exp::mk_false());
            }
            Val { sig }
        }
        _ => unreachable!("default_decl: Expected function"),
    };
    decls.push(Decl::ValDecl(decl));

    (Module { name, decls }, names.summary())
}

pub fn extern_module(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Module, Result<CloneSummary<'tcx>, DefId>) {
    match ctx.externs.term(def_id) {
        Some(_) => {
            let span = ctx.tcx.def_span(def_id);
            match item_type(ctx.tcx, def_id) {
                // the dependencies should be what was already stored in the metadata...
                ItemType::Logic | ItemType::Predicate => {
                    (translation::logic_or_predicate(ctx, def_id, span).unwrap().body, Err(def_id))
                }
                _ => unreachable!("extern_module: unexpected term for {:?}", def_id),
            }
        }
        None => {
            let (modl, deps) = default_decl(ctx, def_id);
            // Why do we ever want to return `Err` shouldn't `deps` already be correct?
            let deps =
                if ctx.externs.dependencies(def_id).is_some() { Err(def_id) } else { Ok(deps) };
            (modl, deps)
        }
    }
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub(crate) struct ExternSpec<'tcx> {
    // The contract we are attaching
    pub contract: PreContract,
    // Additional predicates we must verify to call this function
    additional_predicates: Vec<Predicate<'tcx>>,
}

impl ExternSpec<'tcx> {
    pub(crate) fn predicates_for(
        &self,
        tcx: TyCtxt<'tcx>,
        sub: SubstsRef<'tcx>,
    ) -> Vec<Predicate<'tcx>> {
        self.additional_predicates.iter().map(|p| p.subst(tcx, sub)).collect()
    }
}

// Must be run before MIR generation.
pub(crate) fn extract_extern_specs_from_item(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: LocalDefId,
) -> (DefId, ExternSpec<'tcx>) {
    let (thir, expr) = ctx.tcx.thir_body(WithOptConstParam::unknown(def_id));
    let thir = thir.borrow();

    let mut visit = ExtractExternItems::new(&thir);

    visit.visit_expr(&thir[expr]);

    let (id, subst) = visit.items.pop().unwrap();

    // The parameters in the extern spec may have been declared in a different order from the original defition
    // However, the must be a permutation of them. We create substitution which allows us to map from the inner
    // definiton to the parameters of the outer definition.
    let inner_subst = InternalSubsts::identity_for_item(ctx.tcx, id);
    let outer_subst = InternalSubsts::identity_for_item(ctx.tcx, def_id.to_def_id());
    let inverse = InternalSubsts::for_item(ctx.tcx, def_id.to_def_id(), |arg, _| {
        let param = outer_subst[arg.index as usize];
        let ix = subst.iter().position(|e| e == param).unwrap();
        inner_subst[ix]
    });

    let contract = crate::specification::contract_of(ctx, def_id.to_def_id()).unwrap();

    // Use the inverse substitution to turn predicates on the outer definition into ones on the inner definition.
    let additional_predicates =
        ctx.tcx.predicates_of(def_id).instantiate(ctx.tcx, inverse).predicates;
    (id, ExternSpec { contract, additional_predicates })
}

// We shouldn't need a full visitor... or an index set, there should be a single item per extern spec method.
struct ExtractExternItems<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    pub items: IndexSet<(DefId, SubstsRef<'tcx>)>,
}

impl ExtractExternItems<'a, 'tcx> {
    pub fn new(thir: &'a Thir<'tcx>) -> Self {
        ExtractExternItems { thir, items: IndexSet::new() }
    }
}

impl thir::visit::Visitor<'a, 'tcx> for ExtractExternItems<'a, 'tcx> {
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
