use crate::function::all_generic_decls_for;
use crate::translation::translate_logic_or_predicate;
use crate::util::item_type;
use crate::{ctx::*, util};
use rustc_hir::def_id::DefId;
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
            if !ctx.externs.verified(def_id) {
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
