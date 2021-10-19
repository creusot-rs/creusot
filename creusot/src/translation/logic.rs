use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Logic, Module, Predicate, ValKind};

use crate::function::all_generic_decls_for;
use crate::translation::specification;
use crate::{ctx::*, util};

pub fn translate_logic(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    _span: rustc_span::Span,
) -> (Module, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, false);
    names.clone_self(def_id);

    let sig = crate::util::signature_of(ctx, &mut names, def_id);
    let name = translate_value_id(ctx.tcx, def_id).module_ident().unwrap().clone();

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));

    if util::is_trusted(ctx.tcx, def_id) {
        decls.push(Decl::ValDecl(ValKind::Function { sig }));
        return (Module { name, decls }, names);
    }

    let term = ctx.term(def_id).unwrap().clone();

    let body = specification::lower(ctx, &mut names, def_id, term);

    decls.extend(names.to_clones(ctx));
    decls.push(Decl::LogicDecl(Logic { sig, body }));

    (Module { name, decls }, names)
}

pub fn translate_predicate(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    _span: rustc_span::Span,
) -> (Module, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, false);
    names.clone_self(def_id);

    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    sig.retty = None;
    let name = translate_value_id(ctx.tcx, def_id).module_ident().unwrap().clone();

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));

    if util::is_trusted(ctx.tcx, def_id) {
        decls.push(Decl::ValDecl(ValKind::Predicate { sig }));
        return (Module { name, decls }, names);
    }

    let term = ctx.term(def_id).unwrap().clone();
    let mut body = specification::lower(ctx, &mut names, def_id, term);

    decls.extend(names.to_clones(ctx));
    decls.push(Decl::PredDecl(Predicate { sig, body }));

    (Module { name, decls }, names)
}
