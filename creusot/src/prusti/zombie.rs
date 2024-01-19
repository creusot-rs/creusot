use crate::prusti::{
    ctx::{CtxRef, InternedInfo},
    typeck::TypeVarVisitor,
    util::{name_to_def_id, RegionReplacer},
};
use rustc_index::bit_set::BitSet;
use rustc_middle::ty::{
    ParamEnv, Region, Ty, TyCtxt, TyKind, TypeFoldable, TypeSuperVisitable, TypeVisitable,
    TypeVisitor,
};
use rustc_span::def_id::DefId;
use std::ops::ControlFlow;

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
    snap_eq: DefId,
}

impl ZombieDefIds {
    pub fn new(tcx: TyCtxt<'_>) -> ZombieDefIds {
        ZombieDefIds {
            internal: name_to_def_id(tcx, "prusti_zombie_internal"),
            snap_eq: name_to_def_id(tcx, "prusti_snap_eq"),
        }
    }

    pub(super) fn mk_zombie_raw<'tcx>(&self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        let did = self.internal;
        tcx.mk_adt(tcx.adt_def(did), tcx.mk_substs(&[ty.into()]))
    }

    pub(super) fn as_zombie<'tcx>(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            TyKind::Adt(def, subst) if def.did() == self.internal => Some(subst[0].expect_ty()),
            _ => None,
        }
    }

    pub(super) fn is_snap_eq<'tcx>(&self, ty: Ty<'tcx>, ctx: CtxRef<'_, 'tcx>) -> bool {
        ty.visit_with(&mut HasZombieVisitor { def_ids: self, ctx }).is_continue()
    }

    pub fn snap_eq(&self) -> DefId {
        self.snap_eq
    }

    pub fn find_snap_eq_vars(&self, param_env: ParamEnv<'_>, size: usize) -> BitSet<u32> {
        let mut vars = BitSet::new_empty(size);
        for clause in param_env.caller_bounds() {
            match clause.as_trait_clause() {
                Some(x) if x.def_id() == self.snap_eq => {
                    let _ = x.self_ty().visit_with(&mut TypeVarVisitor(&mut vars));
                }
                _ => {}
            }
        }
        vars
    }
}

struct HasZombieVisitor<'a, 'tcx> {
    def_ids: &'a ZombieDefIds,
    ctx: CtxRef<'a, 'tcx>,
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for HasZombieVisitor<'a, 'tcx> {
    type BreakTy = ();
    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if self.def_ids.as_zombie(t).is_some() {
            ControlFlow::Break(())
        } else {
            match t.kind() {
                TyKind::Param(p) => {
                    if !self.ctx.snap_eq_var(p.index) {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                }
                _ => t.super_visit_with(self),
            }
        }
    }
}
