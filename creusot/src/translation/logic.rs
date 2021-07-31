use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Module, Use};

use crate::ctx::*;
use crate::translation::specification;


pub fn translate_logic(ctx: &mut TranslationCtx, def_id: DefId, _span: rustc_span::Span) {
    if !ctx.translated_funcs.insert(def_id) {
        return;
    }

    let body_attr =
        specification::get_attr(ctx.tcx.get_attrs(def_id), &["creusot", "spec", "logic"])
            .unwrap();

    let body = specification::ts_to_symbol(body_attr.args.inner_tokens()).unwrap();
    let p: syn::Term = syn::parse_str(&body).unwrap();

    let module_id = crate::util::parent_module(ctx.tcx, def_id);
    let res = specification::RustcResolver(ctx.resolver.clone(), module_id, ctx.tcx);

    let mut t = pearlite::term::Term::from_syn(&res, p).unwrap();

    let mut pearlite_ctx = pearlite::typing::TypeContext::new_with_ctx(
        specification::RustcContext(ctx.tcx),
        specification::context_at_entry(ctx.tcx, def_id),
    );
    let ret_ty = specification::return_ty(ctx.tcx, def_id);

    pearlite::typing::check_term(&mut pearlite_ctx, &mut t, &ret_ty).unwrap();
    let body = specification::lower_term_to_why(ctx, t);

    let name = crate::ctx::translate_value_id(ctx.tcx, def_id);
    let sig = crate::util::signature_of(ctx, def_id);

    // Gather the required imports
    // TODO: use this to sort logic functions topologically
    // Remove the self-reference and reference to the Type module
    let mut imports = body.qfvs();
    imports.extend(sig.contract.qfvs());
    imports.remove(&name);

    let mut decls: Vec<_> = imports
        .into_iter()
        .map(|qn| qn.module_name())
        .filter(|qn| qn != &crate::modules::type_module())
        .map(|qn| Decl::UseDecl(Use { name: qn }))
        .collect();

    decls.push(Decl::LogicDecl(why3::declaration::Logic { sig, body }));
    let name = translate_value_id(ctx.tcx, def_id).module.join("");

    ctx.modules.add_module(Module { name, decls })
}
