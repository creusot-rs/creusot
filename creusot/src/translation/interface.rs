use why3::{
    declaration::{Decl, Module, ValKind},
    Ident,
};

use crate::{clone_map::CloneMap, ctx::*, translation::function::all_generic_decls_for, util};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub struct Interface {
    pub module: Module,
}

pub fn interface_for(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Interface, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, ItemType::Interface);

    let mut sig = util::signature_of(ctx, &mut names, def_id);

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();

    decls.extend(names.clone().to_clones(ctx));

    decls.push(Decl::ValDecl(match util::item_type(ctx.tcx, def_id) {
        ItemType::Predicate => {
            sig.retty = None;
            ValKind::Predicate { sig }
        }
        ItemType::Logic => ValKind::Function { sig },
        _ => ValKind::Val { sig },
    }));

    let name = interface_name(ctx.tcx, def_id);

    (Interface { module: Module { name, decls } }, names)
}

pub fn interface_name(tcx: TyCtxt, def_id: DefId) -> Ident {
    let name = translate_value_id(tcx, def_id);

    format!("{}_Interface", &*name.module_name().name).into()
}
