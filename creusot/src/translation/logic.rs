use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use why3::declaration::{Decl, Logic, Module, Predicate, Use};
use why3::mlcfg::QName;

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

    let p = get_logic_body(ctx.tcx, def_id).unwrap();

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

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
    let func = Decl::LogicDecl(Logic { sig, body });

    decls.extend(imports_for(&func, name.clone()));
    decls.push(func);

    let name = translate_value_id(ctx.tcx, def_id).module.join("");
    ctx.modules.add_module(Module { name, decls })
}

pub fn translate_predicate(ctx: &mut TranslationCtx, def_id: DefId, _span: rustc_span::Span) {
    if !ctx.translated_funcs.insert(def_id) {
        return;
    }

    let p: syn::Term = get_predicate_body(ctx.tcx, def_id).unwrap();

    let module_id = crate::util::parent_module(ctx.tcx, def_id);
    let res = specification::RustcResolver(ctx.resolver.clone(), module_id, ctx.tcx);

    let mut t = pearlite::term::Term::from_syn(&res, p).unwrap();

    let mut pearlite_ctx = pearlite::typing::TypeContext::new_with_ctx(
        specification::RustcContext(ctx.tcx),
        specification::context_at_entry(ctx.tcx, def_id),
    );
    // TODO: Enforce this to be bool
    let ret_ty = specification::return_ty(ctx.tcx, def_id);

    pearlite::typing::check_term(&mut pearlite_ctx, &mut t, &ret_ty).unwrap();
    let body = specification::lower_term_to_why(ctx, t);

    let name = crate::ctx::translate_value_id(ctx.tcx, def_id);
    let mut sig = crate::util::signature_of(ctx, def_id);
    sig.retty = None;

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();

    let func = Decl::PredDecl(Predicate { sig, body });
    decls.extend(imports_for(&func, name.clone()));

    decls.push(func);
    let name = translate_value_id(ctx.tcx, def_id).module.join("");

    ctx.modules.add_module(Module { name, decls })
}

fn imports_for(decl: &Decl, except: QName) -> impl Iterator<Item = Decl> {
    let mut imports;
    match decl {
        Decl::LogicDecl(Logic { sig, body }) | Decl::PredDecl(Predicate { sig, body }) => {
            imports = body.qfvs();
            imports.extend(sig.contract.qfvs());
            imports.remove(&except); //Why cant i pass in a borrow here?
        }
        _ => unimplemented!("todo: imports_for"),
    }
    imports
        .into_iter()
        .map(|qn| qn.module_name())
        .filter(|qn| qn != &crate::modules::type_module())
        .map(|qn| Decl::UseDecl(Use { name: qn }))
}

fn get_predicate_body(tcx: TyCtxt, pred_id: DefId) -> Option<syn::Term> {
    let body_attr =
        specification::get_attr(tcx.get_attrs(pred_id), &["creusot", "spec", "predicate"])?;

    let body = specification::ts_to_symbol(body_attr.args.inner_tokens())?;
    syn::parse_str(&body).ok()
}

fn get_logic_body(tcx: TyCtxt, logic_id: DefId) -> Option<syn::Term> {
    let body_attr =
        specification::get_attr(tcx.get_attrs(logic_id), &["creusot", "spec", "logic"])?;

    let body = specification::ts_to_symbol(body_attr.args.inner_tokens())?;
    syn::parse_str(&body).ok()
}
