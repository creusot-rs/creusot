use crate::function::all_generic_decls_for;
use crate::util::item_type;
use crate::{ctx::*, util};
use rustc_hir::def_id::DefId;
use why3::declaration::ValKind;
use why3::declaration::{Decl, Module, ValKind::Val};

use super::{translate_logic, translate_predicate};

pub fn default_decl(ctx: &mut TranslationCtx, def_id: DefId) -> Module {
    info!("generating default declaration for def_id={:?}", def_id);
    let mut names =
        CloneMap::new(ctx.tcx, def_id, util::item_type(ctx.tcx, def_id).is_transparent());

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));

    let sig = crate::util::signature_of(ctx, &mut names, def_id);
    let name = translate_value_id(ctx.tcx, def_id).module_ident().unwrap().clone();

    decls.extend(names.to_clones(ctx));
    let decl = match item_type(ctx.tcx, def_id) {
        ItemType::Logic => ValKind::Function { sig },
        ItemType::Predicate => ValKind::Predicate { sig },
        ItemType::Program => Val { sig },
        _ => unreachable!("default_decl: Expected function"),
    };
    decls.push(Decl::ValDecl(decl));

    Module { name, decls }
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
                ItemType::Logic => (translate_logic(ctx, def_id, span).0, Err(def_id)),
                ItemType::Predicate => (translate_predicate(ctx, def_id, span).0, Err(def_id)),

                _ => unreachable!("extern_module: unexpected term for {:?}", def_id),
            }
        }
        None => {
            let modl = default_decl(ctx, def_id);
            let deps = if ctx.externs.dependencies(def_id).is_some() {
                Err(def_id)
            } else {
                Ok(CloneSummary::new())
            };
            (modl, deps)
        }
    }
}
