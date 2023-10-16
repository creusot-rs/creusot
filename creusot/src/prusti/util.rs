use rustc_infer::infer::{InferCtxt, RegionVariableOrigin};
use rustc_middle::ty::{Region, TyCtxt, TypeFoldable, TypeFolder};
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
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        (self.f)(r)
    }
}

pub(super) fn name_to_def_id<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> DefId {
    let map = &tcx.all_diagnostic_items(()).name_to_id;
    map[&Symbol::intern(name)]
}
