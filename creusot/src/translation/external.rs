use crate::function::all_generic_decls_for;
use crate::translation::translate_logic_or_predicate;
use crate::util::item_type;
use crate::{ctx::*, util};
use indexmap::IndexSet;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{TyKind, WithOptConstParam};
use why3::declaration::ValKind;
use why3::declaration::{Decl, Module, ValKind::Val};

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
                    (translate_logic_or_predicate(ctx, def_id, span).0, Err(def_id))
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

type ExternSpec = (DefId, PreContract);
// Must be run before MIR generation.
pub fn extract_extern_specs_from_item(ctx: &mut TranslationCtx, def_id: LocalDefId) -> ExternSpec {
    // let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    // let body = tcx.hir().body(tcx.hir().body_owned_by(hir_id));
    // let mut visitor = ExtractExternItems { items : IndexSet::new() };

    // visitor.visit_body(body);

    let (thir, expr) = ctx.tcx.thir_body(WithOptConstParam::unknown(def_id));
    let thir = thir.borrow();

    let mut visit = ExtractExternItems::new(&thir);

    visit.visit_expr(&thir[expr]);

    let contract = crate::specification::contract_of(ctx, def_id.to_def_id()).unwrap();
    (visit.items.pop().unwrap(), contract)
    // panic!()
}

// use rustc_hir::intravisit::{Visitor, NestedVisitorMap, walk_qpath};
// use rustc_middle::hir::map::Map;
// struct ExtractExternItems {
//     pub items: IndexSet<DefId>,
// }

// impl<'tcx> Visitor<'tcx> for ExtractExternItems {
//     type Map = Map<'tcx>;

//     fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
//         NestedVisitorMap::None
//     }

//     fn visit_qpath(&mut self, qpath: &'v rustc_hir::QPath<'v>, id: rustc_hir::HirId, span: rustc_span::Span) {
//         eprintln!("{:?}\n", qpath);
//         walk_qpath(self, qpath, id, span);

//     }

//     // fn visit_path(&mut self, path: &'v rustc_hir::Path<'v>, _id: rustc_hir::HirId) {
//     //     eprintln!("{:?}\n", path);
//     // }
// }

use rustc_middle::thir::visit::Visitor;
use rustc_middle::thir::{self, Expr, ExprKind, Thir};

use super::specification::PreContract;

// We shouldn't need a full visitor... or an index set, there should be a single item per extern spec method.
struct ExtractExternItems<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    pub items: IndexSet<DefId>,
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
            if let TyKind::FnDef(id, _) = ty.kind() {
                self.items.insert(*id);
            }
        }
        thir::visit::walk_expr(self, expr);
    }
}
