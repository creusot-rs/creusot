use rustc_hir::definitions::DefPath;
use rustc_hir::{def_id::DefId, definitions::DefPathData};
use rustc_middle::ty::TyCtxt;

#[derive(Debug, Clone)]
pub struct ModulePath(pub(crate) DefPath);

pub fn module_of(tcx: TyCtxt<'_>, def_id: DefId) -> ModulePath {
    let mut def_path = tcx.def_path(def_id);
    def_path.data.pop();

    while !def_path.data.is_empty() {
        match def_path.data.pop().unwrap().data {
            DefPathData::ClosureExpr | DefPathData::Impl | DefPathData::ImplTrait => { }
            _ => { break }
        }
    }

    ModulePath(def_path)
}
