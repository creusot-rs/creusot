use crate::prusti::util::{name_to_def_id, RegionReplacer};
use rustc_middle::ty::{ParamEnv, Region, Ty, TyCtxt, TyKind, TypeFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitor};
use rustc_span::def_id::DefId;
use std::ops::ControlFlow;
use crate::prusti::ctx::InternedInfo;

#[derive(Copy, Clone, Debug)]
pub enum ZombieStatus {
    Zombie,
    NonZombie,
}

pub(super) fn fixing_replace<'tcx, F, T>(ctx: &InternedInfo<'tcx>, f: F, ty: T) -> T
    where
        F: FnMut(Region<'tcx>) -> Region<'tcx>,
        T: TypeFoldable<TyCtxt<'tcx>>,
{
    ty.fold_with(&mut RegionReplacer { tcx: ctx.tcx, f })
}

pub(super) fn pretty_replace<'tcx, F, T>(ctx: &InternedInfo<'tcx>, f: F, ty: T) -> T
    where
        F: FnMut(Region<'tcx>) -> Region<'tcx>,
        T: TypeFoldable<TyCtxt<'tcx>>,
{
    ty.fold_with(&mut RegionReplacer { tcx: ctx.tcx, f })
}


pub struct ZombieDefIds {
    internal: DefId,
}

impl ZombieDefIds {
    pub fn new(tcx: TyCtxt<'_>) -> ZombieDefIds {
        ZombieDefIds { internal: name_to_def_id(tcx, "prusti_zombie_internal") }
    }

    pub(super) fn mk_zombie_raw<'tcx>(
        &self,
        ty: Ty<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Ty<'tcx> {
        let did = self.internal;
        tcx.mk_adt(tcx.adt_def(did), tcx.mk_substs(&[ty.into()]))
    }

    /// Makes a type copy by wrapping parts of it in Zombie
    /// result.1 is true iff the type was changed
    pub(super) fn mk_zombie<'tcx>(
        &self,
        ty: Ty<'tcx>,
        tcx: TyCtxt<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> (Ty<'tcx>, bool) {
        if ty.is_copy_modulo_regions(tcx, param_env) {
            (ty, false)
        } else {
            let ty = self.mk_zombie_raw(ty, tcx);
            (ty, true)
        }
    }

    pub(super) fn as_zombie<'tcx>(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            TyKind::Adt(def, subst) if def.did() == self.internal => Some(subst[0].expect_ty()),
            _ => None,
        }
    }

    pub fn contains_zombie(&self, ty: Ty<'_>) -> bool {
        ty.visit_with(&mut HasZombieVisitor { def_ids: self }).is_break()
    }
}

struct HasZombieVisitor<'a> {
    def_ids: &'a ZombieDefIds,
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for HasZombieVisitor<'a> {
    type BreakTy = ();
    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if self.def_ids.as_zombie(t).is_some() {
            ControlFlow::Break(())
        } else {
            t.super_visit_with(self)
        }
    }
}
