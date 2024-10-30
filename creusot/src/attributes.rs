use std::collections::HashMap;

use rustc_ast::{
    visit::{walk_fn, FnKind, Visitor},
    AttrArgs, AttrArgsEq, AttrItem, Attribute, FnSig, NodeId,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{ResolverAstLowering, Ty, TyCtxt, TyKind};
use rustc_span::{Span, Symbol};

pub(crate) fn no_mir(tcx: TyCtxt, def_id: DefId) -> bool {
    is_no_translate(tcx, def_id) || is_predicate(tcx, def_id) || is_logic(tcx, def_id)
}

pub(crate) fn is_pearlite(tcx: TyCtxt, def_id: DefId) -> bool {
    is_predicate(tcx, def_id)
        || is_spec(tcx, def_id)
        || is_logic(tcx, def_id)
        || is_assertion(tcx, def_id)
        || is_snapshot_closure(tcx, def_id)
}

pub(crate) fn is_no_translate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "no_translate"]).is_some()
}

pub(crate) fn is_spec(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec"]).is_some()
}

pub(crate) fn is_invariant(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "invariant"]).is_some()
}

pub(crate) fn is_loop_variant(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "variant", "loop_"]).is_some()
}

pub(crate) fn is_variant(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "variant"]).is_some()
}

pub(crate) fn is_assertion(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "assert"]).is_some()
}

pub(crate) fn is_snapshot_closure(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "snapshot"]).is_some()
}

pub(crate) fn is_ghost_closure(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "ghost"]).is_some()
}

pub(crate) fn snapshot_closure_id<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<DefId> {
    if let TyKind::Closure(def_id, _) = ty.peel_refs().kind() {
        if is_snapshot_closure(tcx, *def_id) {
            return Some(*def_id);
        }
    }
    None
}

pub(crate) fn is_snap_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let r: Option<bool> = try {
        let adt = ty.ty_adt_def()?;
        let builtin = get_builtin(tcx, adt.did())?;
        builtin.as_str() == "prelude.prelude.Snapshot.snap_ty"
    };
    r.unwrap_or(false)
}

pub(crate) fn is_logic(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "logic"]).is_some()
}

pub(crate) fn is_prophetic(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "logic", "prophetic"]).is_some()
}

pub(crate) fn is_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "predicate"]).is_some()
}

pub(crate) fn is_trusted(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "trusted"]).is_some()
}

pub(crate) fn is_law(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "law"]).is_some()
}

pub(crate) fn should_replace_trigger(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "no_trigger"]).is_none()
}

pub(crate) fn is_extern_spec(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "extern_spec"]).is_some()
}

pub(crate) fn is_ignore_structural_inv(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "trusted_ignore_structural_inv"])
        .is_some()
}

pub(crate) fn is_tyinv_trivial_if_param_trivial(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["creusot", "trusted_is_tyinv_trivial_if_param_trivial"],
    )
    .is_some()
}

pub(crate) fn has_variant_clause(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "clause", "variant"]).is_some()
}

pub(crate) fn is_open_inv_result(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "open_inv_result"]).is_some()
}

pub(crate) fn is_inv(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.is_diagnostic_item(Symbol::intern("creusot_invariant_internal"), def_id)
}

#[allow(dead_code)]
pub(crate) fn is_invariant_method(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.is_diagnostic_item(Symbol::intern("creusot_invariant_user"), def_id)
}

#[allow(dead_code)]
pub(crate) fn is_resolve_method(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
}

pub(crate) fn is_resolve_function(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.is_diagnostic_item(Symbol::intern("creusot_resolve"), def_id)
}

pub(crate) fn opacity_witness_name(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "clause", "open"]).and_then(|item| {
        match &item.args {
            AttrArgs::Eq(_, AttrArgsEq::Hir(l)) => Some(l.symbol),
            _ => None,
        }
    })
}

pub(crate) fn why3_attrs(tcx: TyCtxt, def_id: DefId) -> Vec<why3::declaration::Attribute> {
    let matches = get_attrs(tcx.get_attrs_unchecked(def_id), &["why3", "attr"]);
    matches
        .into_iter()
        .map(|a| why3::declaration::Attribute::Attr(a.value_str().unwrap().as_str().into()))
        .collect()
}

pub(crate) fn creusot_clause_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    clause: &str,
) -> impl Iterator<Item = &'tcx AttrArgs> {
    // Attributes are given in reverse order. So we need to rever the list of
    // attributes to make sure requires/ensures clauses appear in the same
    // order in WhyML code as they appear in Rust code.
    get_attrs(tcx.get_attrs_unchecked(def_id), &["creusot", "clause", clause])
        .into_iter()
        .rev()
        .map(|a| &a.get_normal_item().args)
}

pub(crate) fn get_creusot_item(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    match &get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "item"])?.args {
        AttrArgs::Eq(_, AttrArgsEq::Hir(l)) => Some(l.symbol),
        _ => unreachable!("invalid creusot::item attribute"),
    }
}

pub(crate) fn should_translate(tcx: TyCtxt, mut def_id: DefId) -> bool {
    loop {
        if is_no_translate(tcx, def_id) {
            return false;
        }

        if tcx.is_closure_like(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            return true;
        }
    }
}

pub(crate) fn get_builtin(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "builtins"]).and_then(|a| {
        match &a.args {
            AttrArgs::Eq(_, AttrArgsEq::Hir(l)) => Some(l.symbol),
            _ => None,
        }
    })
}

pub(crate) fn get_attr<'a>(attrs: &'a [Attribute], path: &[&str]) -> Option<&'a AttrItem> {
    for attr in attrs.iter() {
        if attr.is_doc_comment() {
            continue;
        }

        let attr = attr.get_normal_item();

        if attr.path.segments.len() != path.len() {
            continue;
        }

        let matches =
            attr.path.segments.iter().zip(path.iter()).all(|(seg, s)| &*seg.ident.as_str() == *s);

        if matches {
            return Some(attr);
        }
    }
    None
}

pub(crate) fn get_attrs<'a>(attrs: &'a [Attribute], path: &[&str]) -> Vec<&'a Attribute> {
    let mut matched = Vec::new();

    for attr in attrs.iter() {
        if attr.is_doc_comment() {
            continue;
        }

        let item = attr.get_normal_item();

        if item.path.segments.len() != path.len() {
            continue;
        }

        let matches =
            item.path.segments.iter().zip(path.iter()).all(|(seg, s)| &*seg.ident.as_str() == *s);

        if matches {
            matched.push(attr)
        }
    }
    matched
}

pub(crate) fn gather_params_open_inv(tcx: TyCtxt) -> HashMap<DefId, Vec<usize>> {
    struct VisitFns<'a>(HashMap<DefId, Vec<usize>>, &'a ResolverAstLowering);
    impl<'a> Visitor<'a> for VisitFns<'a> {
        fn visit_fn(&mut self, fk: FnKind<'a>, _: Span, node: NodeId) {
            let decl = match fk {
                FnKind::Fn(_, _, FnSig { decl, .. }, _, _, _) => decl,
                FnKind::Closure(_, decl, _) => decl,
            };
            let mut open_inv_params = vec![];
            for (i, p) in decl.inputs.iter().enumerate() {
                if get_attr(&p.attrs, &["creusot", "open_inv"]).is_some() {
                    open_inv_params.push(i);
                }
            }
            let defid = self.1.node_id_to_def_id[&node].to_def_id();
            assert!(self.0.insert(defid, open_inv_params).is_none());
            walk_fn(self, fk)
        }
    }

    let (resolver, cr) = &*tcx.resolver_for_lowering().borrow();

    let mut visit = VisitFns(HashMap::new(), &resolver);
    visit.visit_crate(&*cr);
    visit.0
}
