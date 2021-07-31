use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Val, Module};
use super::logic::*;

use crate::ctx::*;
use crate::translation::specification;
use crate::function::all_generic_decls_for;

// Translate functions that are external to the crate as opaque values
pub fn translate_extern(ctx: &mut TranslationCtx, def_id: DefId, span: rustc_span::Span) {
    if !ctx.translated_funcs.insert(def_id) {
        return;
    }

    if specification::get_attr(ctx.tcx.get_attrs(def_id), &["creusot", "spec", "logic"])
        .is_some()
    {
        translate_logic(ctx, def_id, span);
        return;
    }

    let sig = crate::util::signature_of(ctx, def_id);

    let name = translate_value_id(ctx.tcx, def_id).module.join("");

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
    decls.push(Decl::ValDecl(Val { sig }));

    ctx.modules.add_module(Module { name, decls });
}
