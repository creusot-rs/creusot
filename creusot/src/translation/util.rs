use rustc_ast::AttrItem;
use rustc_middle::ty::Attributes;

fn is_attr(attr: &AttrItem, str: &str) -> bool {
    let segments = &attr.path.segments;
    segments.len() >= 2
        && segments[0].ident.as_str() == "creusot"
        && segments[1].ident.as_str() == str
}

pub fn spec_attrs<'tcx>(a: Attributes<'tcx>) -> Vec<&AttrItem> {
    a.iter()
        .filter(|a| !a.is_doc_comment())
        .map(|a| a.get_normal_item())
        .filter(|ai| is_attr(ai, "spec"))
        .collect()
}

use rustc_hir::definitions::DefPath;
use rustc_hir::{
    def_id::DefId,
    definitions::DefPathData,
};
use rustc_middle::ty::TyCtxt;

#[derive(Clone)]
pub struct ModulePath(pub(crate) DefPath);

pub fn module_of<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> ModulePath {
  let mut def_path = tcx.def_path(def_id);
  let mut layers = 1;

  while layers > 0 {
      match def_path.data.last().unwrap().data {
        DefPathData::ClosureExpr => layers += 1,
        _ => {},
      }
      def_path.data.pop();
      layers -= 1;
  }

  ModulePath(def_path)
}
