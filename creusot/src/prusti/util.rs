use rustc_infer::infer::{InferCtxt, RegionVariableOrigin};
use rustc_middle::ty::{
    InferTy, Region, Ty, TyCtxt, TyKind, TyVid, TypeFoldable, TypeFolder, TypeSuperFoldable,
};
use rustc_span::{def_id::DefId, Symbol, DUMMY_SP};

pub(super) fn generalize<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(t: T, infcx: &InferCtxt<'tcx>) -> T {
    t.fold_with(&mut RegionReplacer {
        tcx: infcx.tcx,
        f: |_| infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP)),
    })
}

pub(super) struct RegionReplacer<'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> {
    pub tcx: TyCtxt<'tcx>,
    pub f: F,
}

impl<'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> TypeFolder<TyCtxt<'tcx>>
    for RegionReplacer<'tcx, F>
{
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        (self.f)(r)
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        match t.kind() {
            TyKind::Infer(InferTy::FreshTy(x)) => Ty::new_var(self.tcx, TyVid::from(*x)),
            _ => t.super_fold_with(self),
        }
    }
}

pub(super) fn name_to_def_id<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> DefId {
    let map = &tcx.all_diagnostic_items(()).name_to_id;
    map[&Symbol::intern(name)]
}
