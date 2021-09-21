use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Logic, Module, Predicate};

use crate::ctx::*;
use crate::function::all_generic_decls_for;
use crate::translation::specification;

pub fn translate_logic(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    _span: rustc_span::Span,
) -> (Module, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, ItemType::Logic);
    names.clone_self(def_id);

    let term = specification::typing::typecheck(ctx.tcx, def_id.expect_local());
    let body = specification::lower_term_to_why3(ctx, &mut names, def_id, term);
    let sig = crate::util::signature_of(ctx, &mut names, def_id);

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.clone().to_clones(ctx));

    let func = Decl::LogicDecl(Logic { sig, body });

    decls.push(func);

    let name = translate_value_id(ctx.tcx, def_id).module_name().name();
    (Module { name, decls }, names)
}

pub fn translate_predicate(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    _span: rustc_span::Span,
) -> (Module, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, ItemType::Predicate);
    names.clone_self(def_id);

    let term = specification::typing::typecheck(ctx.tcx, def_id.expect_local());
    let body = specification::lower_term_to_why3(ctx, &mut names, def_id, term);
    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    sig.retty = None;

    let func = Decl::PredDecl(Predicate { sig, body });

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.clone().to_clones(ctx));
    decls.push(func);

    let name = translate_value_id(ctx.tcx, def_id).module_name().name();
    (Module { name, decls }, names)
}
