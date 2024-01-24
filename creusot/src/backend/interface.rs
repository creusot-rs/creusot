use super::{clone_map::CloneMap, CloneSummary, Why3Generator};
use crate::{
    backend::{
        closure_generic_decls,
        logic::{spec_axiom, val_decl},
        signature::signature_of,
    },
    ctx::*,
    util,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{ClosureKind, TyKind};
use std::borrow::Cow;
use why3::{
    declaration::{Contract, Decl, Module},
    Exp, Ident,
};
pub(crate) fn interface_for<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (Module, CloneSummary<'tcx>) {
    debug!("interface_for: {def_id:?}");
    let mut names = CloneMap::new(ctx.tcx, def_id.into());
    let mut sig = signature_of(ctx, &mut names, def_id);

    sig.contract.variant = Vec::new();

    let mut decls = Vec::new();

    if ctx.tcx.is_closure(def_id) {
        if let TyKind::Closure(_, subst) = ctx.tcx.type_of(def_id).subst_identity().kind() {
            if subst.as_closure().kind() == ClosureKind::FnMut {
                sig.contract.ensures.push(
                    Exp::pure_var("unnest".into())
                        .app_to(Exp::Current(Box::new(Exp::pure_var("_1".into()))))
                        .app_to(Exp::Final(Box::new(Exp::pure_var("_1".into())))),
                )
            }
        }
    }

    match util::item_type(ctx.tcx, def_id) {
        ItemType::Predicate => {
            let sig_contract = sig.clone();
            sig.retty = None;
            sig.contract = Contract::new();
            decls.push(Decl::ValDecl(util::item_type(ctx.tcx, def_id).val(sig)));
            decls.push(val_decl(ctx, &mut names, def_id));
            let has_axioms = !sig_contract.contract.ensures.is_empty();
            if has_axioms {
                decls.push(Decl::Axiom(spec_axiom(&sig_contract)));
            }
        }
        ItemType::Ghost | ItemType::Logic => {
            let sig_contract = sig.clone();
            sig.contract = Contract::new();
            decls.push(Decl::ValDecl(util::item_type(ctx.tcx, def_id).val(sig)));
            decls.push(val_decl(ctx, &mut names, def_id));

            let has_axioms = !sig_contract.contract.ensures.is_empty();
            if has_axioms {
                decls.push(Decl::Axiom(spec_axiom(&sig_contract)));
            }
        }
        _ => {
            decls.push(Decl::ValDecl(util::item_type(ctx.tcx, def_id).val(sig)));
        }
    }

    let name = interface_name(ctx, def_id);
    let (clones, summary) = names.to_clones(ctx, CloneDepth::Shallow);
    let decls = closure_generic_decls(ctx.tcx, def_id).chain(clones).chain(decls).collect();

    (Module { name, decls }, summary)
}

pub(crate) fn interface_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
    format!("{}_Interface", Cow::from(&*module_name(ctx.tcx, def_id))).into()
}
