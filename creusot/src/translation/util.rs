use rustc_hir::definitions::DefPath;
use rustc_hir::{def_id::DefId, definitions::DefPathData};
use rustc_middle::ty::TyCtxt;

#[derive(Clone)]
pub struct ModulePath(pub(crate) DefPath);

pub fn module_of(tcx: TyCtxt<'_>, def_id: DefId) -> ModulePath {
    let mut def_path = tcx.def_path(def_id);
    let mut layers = 1;

    while layers > 0 {
        if let DefPathData::ClosureExpr = def_path.data.last().unwrap().data {
            layers += 1
        }
        def_path.data.pop();
        layers -= 1;
    }

    ModulePath(def_path)
}
