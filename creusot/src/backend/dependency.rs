use rustc_hir::def_id::DefId;
use rustc_middle::ty::{ParamEnv, SubstsRef, Ty, TyCtxt, TyKind};
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

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item((DefId, SubstsRef<'tcx>)),
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, dep: (DefId, SubstsRef<'tcx>)) -> Self {
        match util::item_type(tcx, dep.0) {
            ItemType::Type => Dependency::Type(tcx.mk_adt(tcx.adt_def(dep.0), dep.1)),
            // ItemType::Closure => Dependency::Type(tcx.type_of(dep.0).subst(tcx, dep.1)),
            ItemType::AssocTy => Dependency::Type(tcx.mk_projection(dep.0, dep.1)),
            _ => Dependency::Item(dep),
        }
    }

    pub(crate) fn resolve(
        self,
        ctx: &TranslationCtx<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<Self> {
        match self {
            Dependency::Type(ty) => resolve_type(ty, ctx.tcx, param_env),
            Dependency::Item((item, substs)) => resolve_item(item, substs, ctx.tcx, param_env),
        }
    }

    pub(crate) fn cloneable_id(self) -> Option<(DefId, SubstsRef<'tcx>)> {
        match self {
            Dependency::Item(i) => Some(i),
            Dependency::Type(t) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasKind::Projection, aty) => Some((aty.def_id, aty.substs)),
                _ => None,
            },
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
    Some(Dependency::Item(normed))
}

fn closure_hack<'tcx>(
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
