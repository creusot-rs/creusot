// Should probably be folded into a different module
//
//
use crate::{
    backend::ty,
    ctx::*,
    util::{item_type, why3_attrs},
};
use creusot_rustc::{
    self,
    hir::def_id::DefId,
    resolve::Namespace,
    span::{Symbol, DUMMY_SP},
};
use why3::{declaration, declaration::Signature, exp::Binder, ty::Type};

use crate::{
    ctx::{item_name, TranslationCtx},
    util::{ident_of, pre_sig_of},
};

use super::clone_map2::Names;

pub(crate) fn signature_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &Names<'tcx>,
    def_id: DefId,
) -> Signature {
    debug!("signature_of {def_id:?}");
    let pre_sig = pre_sig_of(ctx, def_id);

    let contract = pre_sig.contract.to_exp2(ctx, names, def_id);

    let name = item_name(ctx.tcx, def_id, Namespace::ValueNS);

    let span = ctx.tcx.def_span(def_id);
    let mut args: Vec<Binder> = pre_sig
        .inputs
        .into_iter()
        .enumerate()
        .map(|(ix, (id, ty))| {
            let ty = ty::translate_ty(ctx, names, span, ty);
            let id = if id.is_empty() {
                format!("_{}'", ix + 1).into()
            } else if id == Symbol::intern("result") {
                ctx.crash_and_error(DUMMY_SP, "`result` is not allowed as a parameter name");
            } else {
                ident_of(id)
            };
            Binder::typed(id, ty)
        })
        .collect();

    if args.is_empty() {
        args.push(Binder::wild(Type::UNIT));
    };

    let mut attrs = why3_attrs(ctx.tcx, def_id);
    if matches!(item_type(ctx.tcx, def_id), ItemType::Program | ItemType::Closure) {
        attrs.push(declaration::Attribute::Attr("cfg:stackify".into()))
    };

    def_id
        .as_local()
        .map(|d| ctx.def_span(d))
        .and_then(|span| ctx.span_attr(span))
        .map(|attr| attrs.push(attr));

    let retty = ty::translate_ty(ctx, names, span, pre_sig.output);
    Signature { name, attrs, retty: Some(retty), args, contract }
}
