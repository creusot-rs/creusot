use std::ops::ControlFlow;
use rustc_middle::ty::{ParamEnv, Ty, TyCtxt, TyKind, TypeSuperVisitable, TypeVisitable, TypeVisitor};
use rustc_span::{def_id::DefId, Symbol};

pub struct ZombieDefIds {
    internal: DefId,
}

impl ZombieDefIds {
    pub fn new(tcx: TyCtxt<'_>) -> ZombieDefIds {
        let map = &tcx.all_diagnostic_items(()).name_to_id;
        let find_did = |name| map[&Symbol::intern(name)];
        ZombieDefIds {
            internal: find_did("prusti_zombie_internal"),
        }
    }

    /// Makes a type copy by wrapping parts of it in Zombie
    /// result.1 is true iff the type was changed
    pub fn mk_zombie<'tcx>(&self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> (Ty<'tcx>, bool) {
        if ty.is_copy_modulo_regions(tcx, param_env) {
            (ty, false)
        } else {
            let did = self.internal;
            let ty = tcx.mk_adt(tcx.adt_def(did), tcx.mk_substs(&[ty.into()]));
            (ty, true)
        }
    }

    pub fn as_zombie<'tcx>(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            TyKind::Adt(def, subst) if def.did() == self.internal => {
                Some(subst[0].expect_ty())
            }
            _ => None
        }
    }

    pub fn contains_zombie(&self, ty: Ty<'_>) -> bool {
        ty.visit_with(&mut HasZombieVisitor{def_ids: self}).is_break()
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