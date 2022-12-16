use super::{
    function::closure_generic_decls,
};
use crate::{backend::logic::spec_axiom, clone_map::CloneMap, ctx::*, util};
use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{ClosureKind, TyKind},
};
use std::borrow::Cow;
use why3::{
    declaration::{Contract, Decl, Module},
    Exp, Ident,
};

pub(crate) fn interface_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
    format!("{}_Interface", Cow::from(&*module_name(ctx, def_id))).into()
}
