// Should probably be folded into a different module
//
//
use crate::{
    backend::ty,
    ctx::*,
    translation::{
        self,
        specification::{
            typing::{super_visit_mut_term, Literal, Term, TermKind, TermVisitorMut},
            PreContract,
        },
        ty::closure_accessor_name,
    },
    util::{item_type, why3_attrs},
};
use creusot_rustc::{
    ast::{
        ast::{MacArgs, MacArgsEq},
        AttrItem, AttrKind, Attribute,
    },
    hir::{def::DefKind, def_id::DefId, Unsafety},
    middle::ty::{
        subst::{InternalSubsts, SubstsRef},
        DefIdTree, EarlyBinder, ReErased, Subst, Ty, TyCtxt, TyKind, VariantDef,
    },
    resolve::Namespace,
    span::{symbol, Symbol, DUMMY_SP},
};
use indexmap::IndexMap;
use rustc_middle::ty::{ClosureKind, RegionKind};
use std::{
    collections::{HashMap, HashSet},
    iter,
};
use why3::{
    declaration,
    declaration::{Signature, ValKind},
    exp::{super_visit_mut, Binder, Constant, Exp, ExpMutVisitor},
    ty::Type,
    Ident, QName,
};

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
            let id = if id.name.is_empty() {
                format!("_{}'", ix + 1).into()
            } else if id.name == Symbol::intern("result") {
                ctx.crash_and_error(id.span, "`result` is not allowed as a parameter name");
            } else {
                ident_of(id.name)
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
