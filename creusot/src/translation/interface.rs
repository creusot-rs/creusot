use std::borrow::Cow;

use why3::{
    declaration::{Contract, Decl, Module, ValKind},
    Ident,
};

use crate::{clone_map::CloneMap, ctx::*, util};

use creusot_rustc::hir::def_id::DefId;
use creusot_rustc::middle::ty::{ClosureKind, TyCtxt, TyKind};

use super::{
    function::{closure_contract, closure_generic_decls, closure_unnest},
    ty::{closure_accessors, translate_closure_ty},
};

pub fn interface_for<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Module, CloneMap<'tcx>) {
    debug!("interface_for: {def_id:?}");
    let mut names = CloneMap::new(ctx.tcx, def_id, false);
    let mut sig = util::signature_of(ctx, &mut names, def_id);

    sig.contract.variant = Vec::new();

    let mut decls: Vec<_> = closure_generic_decls(ctx.tcx, def_id).collect();

    if ctx.tcx.is_closure(def_id) {
        if let TyKind::Closure(_, subst) = ctx.tcx.type_of(def_id).kind() {
            let tydecl = translate_closure_ty(ctx, &mut names, def_id, subst);
            decls.extend(names.to_clones(ctx));

            let accessors = closure_accessors(ctx, &mut names, def_id, subst.as_closure());
            decls.extend(names.to_clones(ctx));
            decls.push(Decl::TyDecl(tydecl));
            decls.extend(accessors);

            let contracts = closure_contract(ctx, &mut names, def_id);
            decls.extend(names.to_clones(ctx));
            decls.extend(contracts);

            if subst.as_closure().kind() == ClosureKind::FnMut {
                sig.contract.ensures.push(closure_unnest(ctx.tcx, &mut names, def_id, subst))
            }
        }
    }

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
            if !def_id.is_local() && !ctx.externs.verified(def_id) && sig.contract.is_empty() {
                sig.contract.requires.push(why3::exp::Exp::mk_false());
            }

            decls.push(Decl::ValDecl(ValKind::Val { sig }));
        }
    }

    let name = interface_name(ctx.tcx, def_id);

    (Module { name, decls }, names)
}

pub fn interface_name(tcx: TyCtxt, def_id: DefId) -> Ident {
    format!("{}_Interface", Cow::from(&*module_name(tcx, def_id))).into()
}
