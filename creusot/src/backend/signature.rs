use rustc_hir::{def::Namespace, def_id::DefId};
use why3::{
    declaration::{Contract, Signature},
    exp::Binder,
};

use crate::{
    ctx::{CloneMap, TranslationCtx},
    translation::{self, specification::PreContract},
    util::{ident_of, item_name, why3_attrs, AnonymousParamName, PreSignature},
};

use super::term::lower_pure;

pub(crate) fn sig_to_why3<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
) -> Signature {
    let contract = names.with_public_clones(|names| contract_to_why3(pre_sig.contract, ctx, names));

    let name = item_name(ctx.tcx, def_id, Namespace::ValueNS);

    let span = ctx.tcx.def_span(def_id);
    let args: Vec<Binder> = names.with_public_clones(|names| {
        pre_sig
            .inputs
            .into_iter()
            .enumerate()
            .map(|(ix, (id, _, ty))| {
                let ty = translation::ty::translate_ty(ctx, names, span, ty);
                let id = if id.is_empty() {
                    format!("{}", AnonymousParamName(ix)).into()
                } else {
                    ident_of(id)
                };
                Binder::typed(id, ty)
            })
            .collect()
    });

    let mut attrs = why3_attrs(ctx.tcx, def_id);

    def_id
        .as_local()
        .map(|d| ctx.def_span(d))
        .and_then(|span| ctx.span_attr(span))
        .map(|attr| attrs.push(attr));

    let retty = names.with_public_clones(|names| {
        translation::ty::translate_ty(ctx, names, span, pre_sig.output)
    });
    Signature { name, attrs, retty: Some(retty), args, contract }
}

fn contract_to_why3<'tcx>(
    pre: PreContract<'tcx>,
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
) -> Contract {
    let mut out = Contract::new();
    for term in pre.requires {
        out.requires.push(lower_pure(ctx, names, term));
    }
    for term in pre.ensures {
        out.ensures.push(lower_pure(ctx, names, term));
    }

    if let Some(term) = pre.variant {
        out.variant = vec![lower_pure(ctx, names, term)];
    }

    out
}
