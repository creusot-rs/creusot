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
