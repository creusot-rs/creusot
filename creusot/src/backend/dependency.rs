use heck::{ToSnakeCase, ToUpperCamelCase};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{EarlyBinder, InternalSubsts, ParamEnv, SubstsRef, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::AliasKind;

use crate::{
    ctx::TranslationCtx,
    translation::traits,
    util::{self, inv_module_name, ItemType},
};

use super::{ty_inv::TyInvKind, TransId};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
///

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord, TypeVisitable, TypeFoldable)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item(DefId, SubstsRef<'tcx>),
    TyInv(Ty<'tcx>, TyInvKind),
    Hacked(HackedId, DefId, SubstsRef<'tcx>),
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord, TypeVisitable, TypeFoldable)]
pub(crate) enum HackedId {
    PostconditionOnce,
    PostconditionMut,
    Postcondition,
    Precondition,
    Unnest,
    Resolve,
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, (did, subst): (DefId, SubstsRef<'tcx>)) -> Self {
        match util::item_type(tcx, did) {
            ItemType::Type => Dependency::Type(tcx.mk_adt(tcx.adt_def(did), subst)),
            ItemType::AssocTy => Dependency::Type(tcx.mk_projection(did, subst)),
            _ => Dependency::Item(did, subst),
        }
    }

    pub(crate) fn from_trans_id(tcx: TyCtxt<'tcx>, trans_id: TransId) -> Self {
        match trans_id {
            TransId::Item(self_id) => {
                let subst = match tcx.def_kind(self_id) {
                    DefKind::Closure => match tcx.type_of(self_id).subst_identity().kind() {
                        TyKind::Closure(_, subst) => subst,
                        _ => unreachable!(),
                    },
                    _ => InternalSubsts::identity_for_item(tcx, self_id),
                };

                Dependency::new(tcx, (self_id, subst)).erase_regions(tcx)
            }
            TransId::TyInv(inv_kind) => Dependency::TyInv(inv_kind.to_skeleton_ty(tcx), inv_kind),
        }
    }

    pub(crate) fn resolve(
        mut self,
        ctx: &TranslationCtx<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<Self> {
        if let Dependency::Item(item, substs) = self {
            self = resolve_item(item, substs, ctx.tcx, param_env);
        }

        ctx.try_normalize_erasing_regions(param_env, self).ok()
    }

    pub(crate) fn did(self) -> Option<(DefId, SubstsRef<'tcx>)> {
        match self {
            Dependency::Item(def_id, subst) => Some((def_id, subst)),
            Dependency::Type(t) | Dependency::TyInv(t, _) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasKind::Projection, aty) => Some((aty.def_id, aty.substs)),
                _ => None,
            },
            Dependency::Hacked(_, id, substs) => Some((id, substs)),
        }
    }

    pub(crate) fn is_hacked(&self) -> bool {
        matches!(self, Dependency::Hacked(_, _, _))
    }

    #[inline]
    pub(crate) fn erase_regions(self, tcx: TyCtxt<'tcx>) -> Self {
        tcx.erase_regions(self)
    }

    #[inline]
    pub(crate) fn subst(self, tcx: TyCtxt<'tcx>, other: Dependency<'tcx>) -> Self {
        let substs = if let Dependency::TyInv(ty, inv_kind) = other {
            inv_kind.tyinv_substs(tcx, ty)
        } else if let Some((_, substs)) = other.did() {
            substs
        } else {
            return self;
        };

        EarlyBinder::bind(self).subst(tcx, substs)
    }

    #[inline]
    pub(crate) fn closure_hack(self, tcx: TyCtxt<'tcx>) -> Self {
        match self {
            Dependency::Item(did, subst) => {
                let (hacked_id, id, subst) = closure_hack(tcx, did, subst);
                if let Some(hacked_id) = hacked_id {
                    Dependency::Hacked(hacked_id, id, subst)
                } else {
                    Dependency::new(tcx, (id, subst))
                }
            }

            _ => self,
        }
    }

    pub(crate) fn base_ident(self, tcx: TyCtxt<'tcx>) -> Symbol {
        match self {
            Dependency::Type(ty) => {
                let nm = match ty.kind() {
                    TyKind::Adt(def, _) => tcx.item_name(def.did()),
                    TyKind::Alias(_, aty) => tcx.item_name(aty.def_id),
                    _ => Symbol::intern("debug_ty_name"),
                };
                Symbol::intern(&nm.as_str().to_snake_case())
            }
            Dependency::Item(_, _) => {
                let did = self.did().unwrap().0;
                let base = match util::item_type(tcx, did) {
                    ItemType::Impl => tcx.item_name(tcx.trait_id_of_impl(did).unwrap()),
                    ItemType::Closure => Symbol::intern(&format!(
                        "closure{}",
                        tcx.def_path(did).data.last().unwrap().disambiguator
                    )),
                    _ => tcx.item_name(did),
                };
                Symbol::intern(&base.as_str().to_upper_camel_case())
            }
            Dependency::TyInv(_, inv_kind) => Symbol::intern(&*inv_module_name(tcx, inv_kind)),
            Dependency::Hacked(hacked_id, _, _) => match hacked_id {
                HackedId::PostconditionOnce => Symbol::intern("postcondition_once"),
                HackedId::PostconditionMut => Symbol::intern("postcondition_mut"),
                HackedId::Postcondition => Symbol::intern("postcondition"),
                HackedId::Precondition => Symbol::intern("precondition"),
                HackedId::Unnest => Symbol::intern("unnest"),
                HackedId::Resolve => Symbol::intern("resolve"),
            },
        }
    }
}

fn resolve_item<'tcx>(
    item: DefId,
    substs: SubstsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Dependency<'tcx> {
    let resolved = if tcx.trait_of_item(item).is_some()
        && let Some(resolved) = traits::resolve_opt(tcx, param_env, item, substs) {
            resolved
    } else {
        (item, substs)
    };

    let (hacked_id, id, subst) = closure_hack(tcx, resolved.0, resolved.1);
    if let Some(hacked_id) = hacked_id {
        Dependency::Hacked(hacked_id, id, subst)
    } else {
        Dependency::new(tcx, (id, subst))
    }
}

pub(crate) fn closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (Option<HackedId>, DefId, SubstsRef<'tcx>) {
    let hacked = if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id) {
        Some(HackedId::Precondition)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id) {
        Some(HackedId::PostconditionOnce)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id) {
        Some(HackedId::PostconditionMut)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id) {
        Some(HackedId::Postcondition)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_unnest"), def_id) {
        Some(HackedId::Unnest)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id) {
        Some(HackedId::Resolve)
    } else {
        None
    };

    if hacked.is_some() {
        let self_ty = subst.types().nth(1).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (hacked, *id, csubst);
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
    {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (Some(HackedId::Resolve), *id, csubst);
        }
    }

    (None, def_id, subst)
}
