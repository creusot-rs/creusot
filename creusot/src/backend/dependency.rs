use rustc_hir::def_id::DefId;
use rustc_middle::ty::{EarlyBinder, ParamEnv, SubstsRef, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::AliasKind;

use crate::{
    ctx::TranslationCtx,
    translation::traits,
    util::{self, ItemType},
};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
///

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Key<'tcx> {
    pub(crate) did: DefId,
    pub(crate) subst: SubstsRef<'tcx>,
    pub(crate) inv: bool,
}

impl<'tcx> std::fmt::Debug for Key<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:}{:?}{:?}", if self.inv { "Inv:" } else { "" }, &self.did, &self.subst)
    }
}

impl<'tcx> From<(DefId, SubstsRef<'tcx>)> for Key<'tcx> {
    #[inline]
    fn from(value: (DefId, SubstsRef<'tcx>)) -> Self {
        Key { did: value.0, subst: value.1, inv: false }
    }
}

impl<'tcx> Key<'tcx> {
    pub(crate) fn new(did: DefId, subst: SubstsRef<'tcx>, inv: bool) -> Self {
        Key { did, subst, inv }
    }

    #[inline]
    pub(crate) fn erase_regions(mut self, tcx: TyCtxt<'tcx>) -> Self {
        self.subst = tcx.erase_regions(self.subst);
        self
    }

    #[inline]
    pub(crate) fn subst(mut self, tcx: TyCtxt<'tcx>, substs: SubstsRef<'tcx>) -> Self {
        self.subst = EarlyBinder(self.subst).subst(tcx, substs);
        self
    }

    #[inline]
    pub(crate) fn closure_hack(self, tcx: TyCtxt<'tcx>) -> Self {
        let (did, subst) = closure_hack(tcx, self.did, self.subst);
        Key { did, subst, ..self }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item(Key<'tcx>),
    TyInv(Key<'tcx>),
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, dep: Key<'tcx>) -> Self {
        match util::item_type(tcx, dep.did) {
            ItemType::Type if dep.inv => Dependency::TyInv(dep),
            ItemType::Type => Dependency::Type(tcx.mk_adt(tcx.adt_def(dep.did), dep.subst)),
            // ItemType::Closure => Dependency::Type(tcx.type_of(dep.0).subst(tcx, dep.1)),
            ItemType::AssocTy => Dependency::Type(tcx.mk_projection(dep.did, dep.subst)),
            _ => Dependency::Item(dep),
        }

        // if matches!(
        //     tcx.def_kind(id_substs.0),
        //     DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Closure
        // ) {
        //     Dependency::Type(tcx.type_of(id_substs.0).subst(tcx, id_substs.1))
        // } else {
        //     Dependency::Item(id_substs)
        // }
    }

    pub(crate) fn resolve(
        self,
        ctx: &TranslationCtx<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<Self> {
        match self {
            Dependency::Type(ty) => resolve_type(ty, ctx.tcx, param_env),
            Dependency::Item(Key { did: item, subst: substs, .. }) => {
                resolve_item(item, substs, ctx.tcx, param_env)
            }
            dep @ Dependency::TyInv(_) => Some(dep),
        }
    }

    pub(crate) fn cloneable_id(self) -> Option<Key<'tcx>> {
        match self {
            Dependency::Item(i) => Some(i),
            Dependency::Type(t) => match t.kind() {
                TyKind::Adt(def, substs) => Some(Key { did: def.did(), subst: substs, inv: false }),
                TyKind::Closure(id, substs) => Some(Key { did: *id, subst: substs, inv: false }),
                TyKind::Alias(AliasKind::Projection, aty) => {
                    Some(Key { did: aty.def_id, subst: aty.substs, inv: false })
                }
                _ => None,
            },
            Dependency::TyInv(i) => Some(i),
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
    Some(Dependency::new(tcx, normed.into()))
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
