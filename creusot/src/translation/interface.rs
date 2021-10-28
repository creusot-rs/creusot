use std::borrow::Cow;

use why3::{
    declaration::{Contract, Decl, Module, ValKind},
    Ident,
};

use crate::{clone_map::CloneMap, ctx::*, translation::function::all_generic_decls_for, util};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub fn interface_for(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Module, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, false);

    let mut sig = util::signature_of(ctx, &mut names, def_id);
    sig.contract.variant = Vec::new();

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();

    decls.extend(names.to_clones(ctx));

    match util::item_type(ctx.tcx, def_id) {
        ItemType::Predicate => {
            sig.retty = None;
            sig.contract = Contract::new();
            decls.push(Decl::ValDecl(ValKind::Predicate { sig }));
        }
        ItemType::Logic => {
            sig.contract = Contract::new();
            decls.push(Decl::ValDecl(ValKind::Function { sig }));
        }
        _ => {
            if !def_id.is_local() && !ctx.externs.verified(def_id) {
                sig.contract.requires.push(why3::mlcfg::Exp::mk_false());
            }

            decls.push(Decl::ValDecl(ValKind::Val { sig }));
        }
    }

    let name = interface_name(ctx.tcx, def_id);

    (Module { name, decls }, names)
}

pub fn interface_name(tcx: TyCtxt, def_id: DefId) -> Ident {
    let name = translate_value_id(tcx, def_id);

    format!("{}_Interface", Cow::from(name.module_ident().unwrap_or(&name.name()))).into()
}
