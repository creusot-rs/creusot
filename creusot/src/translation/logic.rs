use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use why3::declaration::{Decl, Logic, Module, Predicate};

use crate::ctx::*;
use crate::function::all_generic_decls_for;
use crate::translation::specification;

pub fn is_logic(tcx: TyCtxt, def_id: DefId) -> bool {
    specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "logic"]).is_some()
}

pub fn is_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "predicate"]).is_some()
}

pub fn translate_logic(ctx: &mut TranslationCtx, def_id: DefId, _span: rustc_span::Span) {
    if !ctx.translated_funcs.insert(def_id) {
        return;
    }

    let mut names = NameMap::new(ctx.tcx);

    let term = creusot_contracts::typing::typecheck(ctx.tcx, def_id.expect_local());
    let body = specification::lower_term_to_why3(ctx, &mut names, def_id, term);
    let sig = crate::util::signature_of(ctx, &mut names, def_id);

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();

    for ((def_id, subst), clone_name) in names.into_iter() {
        ctx.translate_function(def_id);
        decls.push(clone_item(ctx, def_id, subst, clone_name));
    }

    let func = Decl::LogicDecl(Logic { sig, body });

    decls.push(func);

    let name = translate_value_id(ctx.tcx, def_id).module.join("");
    ctx.modules.add_module(Module { name, decls })
}

pub fn translate_predicate(ctx: &mut TranslationCtx, def_id: DefId, _span: rustc_span::Span) {
    if !ctx.translated_funcs.insert(def_id) {
        return;
    }

    let mut names = NameMap::new(ctx.tcx);

    let term = creusot_contracts::typing::typecheck(ctx.tcx, def_id.expect_local());
    let body = specification::lower_term_to_why3(ctx, &mut names, def_id, term);
    let sig = crate::util::signature_of(ctx, &mut names, def_id);
    let func = Decl::PredDecl(Predicate { sig, body });

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
    for ((def_id, subst), clone_name) in names.into_iter() {
        ctx.translate_function(def_id);
        decls.push(clone_item(ctx, def_id, subst, clone_name));
    }

    decls.push(func);

    let name = translate_value_id(ctx.tcx, def_id).module.join("");
    ctx.modules.add_module(Module { name, decls })
}
