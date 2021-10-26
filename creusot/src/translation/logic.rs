use rustc_hir::def_id::DefId;

use why3::declaration::{Decl, Logic, Module, Predicate, ValKind};

use crate::function::all_generic_decls_for;
use crate::translation::specification;
use crate::{ctx::*, util};

pub fn translate_logic_or_predicate(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    _span: rustc_span::Span,
) -> (Module, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, false);
    names.clone_self(def_id);

    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
    }

    let name = translate_value_id(ctx.tcx, def_id).module_ident().unwrap().clone();

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));

    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        let val = match util::item_type(ctx.tcx, def_id) {
            ItemType::Logic => ValKind::Function { sig },
            ItemType::Predicate => ValKind::Predicate { sig },
            _ => unreachable!(),
        };

        decls.push(Decl::ValDecl(val));
        return (Module { name, decls }, names);
    }

    let term = ctx.term(def_id).unwrap().clone();

    let body = specification::lower(ctx, &mut names, def_id, term);

    decls.extend(names.to_clones(ctx));
    let decl = match util::item_type(ctx.tcx, def_id) {
        ItemType::Logic => Decl::LogicDecl(Logic { sig, body }),
        ItemType::Predicate => Decl::PredDecl(Predicate { sig, body }),
        _ => unreachable!(),
    };
    decls.push(decl);

    (Module { name, decls }, names)
}
