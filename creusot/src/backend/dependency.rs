use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{EarlyBinder, InternalSubsts, ParamEnv, SubstsRef, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::AliasKind;

use crate::{
    ctx::TranslationCtx,
    translation::traits,
    util::{self, ItemType},
};

use super::{
    ty_inv::{self, TyInvKind},
    TransId,
};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
///

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item(DefId, SubstsRef<'tcx>),
    TyInv(Ty<'tcx>),
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
            TransId::TyInv(inv_kind) => Dependency::TyInv(inv_kind.to_skeleton_ty(tcx)),
        }
    }

    pub(crate) fn resolve(
        self,
        ctx: &TranslationCtx<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<Self> {
        match self {
            Dependency::Type(ty) => resolve_type(ty, ctx.tcx, param_env),
            Dependency::Item(item, substs) => resolve_item(item, substs, ctx.tcx, param_env),
            dep @ Dependency::TyInv(_) => Some(dep),
        }
    }

    pub(crate) fn did(self) -> Option<(DefId, SubstsRef<'tcx>)> {
        match self {
            Dependency::Item(def_id, subst) => Some((def_id, subst)),
            Dependency::Type(t) | Dependency::TyInv(t) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasKind::Projection, aty) => Some((aty.def_id, aty.substs)),
                _ => None,
            },
        }
    }

    pub(crate) fn ty_inv_kind(self) -> Option<TyInvKind> {
        if let Dependency::TyInv(ty) = self {
            Some(TyInvKind::from_ty(ty))
        } else {
            None
        }
    }

    pub(crate) fn is_inv(&self) -> bool {
        matches!(self, Dependency::TyInv(_))
    }

    #[inline]
    pub(crate) fn erase_regions(mut self, tcx: TyCtxt<'tcx>) -> Self {
        match &mut self {
            Dependency::Item(_, s) => *s = tcx.erase_regions(*s),
            Dependency::Type(ty) | Dependency::TyInv(ty) => *ty = tcx.erase_regions(*ty),
        };
        self
    }

    #[inline]
    pub(crate) fn subst(mut self, tcx: TyCtxt<'tcx>, other: Dependency<'tcx>) -> Self {
        let substs = if let Dependency::TyInv(ty) = other {
            ty_inv::tyinv_substs(tcx, ty)
        } else if let Some((_, substs)) = other.did() {
            substs
        } else {
            return self;
        };

        match &mut self {
            Dependency::Item(_, s) => *s = EarlyBinder(*s).subst(tcx, substs),
            Dependency::Type(ty) | Dependency::TyInv(ty) => {
                *ty = EarlyBinder(*ty).subst(tcx, substs)
            }
        };
        self
    }

    #[inline]
    pub(crate) fn closure_hack(self, tcx: TyCtxt<'tcx>) -> Self {
        match self {
            Dependency::Item(did, subst) => Dependency::new(tcx, closure_hack(tcx, did, subst)),
            _ => self,
        }
    }
}

fn resolve_type<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<Dependency<'tcx>> {
    let normed = tcx.try_normalize_erasing_regions(param_env, ty);
    match normed {
        Ok(ty) => Some(Dependency::Type(ty)),
        Err(_) => None,
    }
}

fn resolve_item<'tcx>(
    item: DefId,
    substs: SubstsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<Dependency<'tcx>> {
    let resolved = if tcx.impl_of_method(item).is_some() {
        (item, substs)
    } else {
        traits::resolve_opt(tcx, param_env, item, substs)?
    };
    let resolved = closure_hack(tcx, resolved.0, resolved.1);
    let normed = tcx.try_normalize_erasing_regions(param_env, resolved).unwrap();
    Some(Dependency::new(tcx, normed))
}

pub(crate) fn closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (DefId, SubstsRef<'tcx>) {
    if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_unnest"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id)
    {
        let self_ty = subst.types().nth(1).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (*id, csubst);
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
    {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (*id, csubst);
        }
    }

    (def_id, subst)
}
