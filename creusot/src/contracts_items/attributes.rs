//! Defines all the internal creusot attributes.

use rustc_ast::Param;
use rustc_hir::{def_id::DefId, AttrArgs, Attribute};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

/// Helper macro, converts `creusot::foo::bar` into `["creusot", "foo", "bar"]`.
macro_rules! path_to_str {
    ([ :: $($p:tt)* ] ; [ $($acc:expr,)* ]) => {
        path_to_str!([ $($p)* ] ; [ $($acc,)* ])
    };
    ([ $x:tt $($p:tt)* ] ; [ $($acc:expr,)* ]) => {
        path_to_str!([ $($p)* ] ; [ $($acc,)* stringify!($x), ])
    };
    ([ ] ; [ $($acc:expr,)* ]) => { [$($acc),*] };
    ($($p:tt)*) => { path_to_str!([ $($p)* ] ; []) };
}

macro_rules! attribute_functions {
    (
        $(
            $($not:ident)? [ $($p:tt)* ] => $fn_name:ident
        )+
    ) => {
        $(
            #[doc = concat!("Detect if `def_id` has the attribute `", stringify!($($p)*), "`")]
            pub(crate) fn $fn_name(tcx: TyCtxt, def_id: DefId) -> bool {
                let path = &path_to_str!($($p)*);
                let has_attr = get_attr(tcx, tcx.get_attrs_unchecked(def_id), path).is_some();
                attribute_functions!(@negate $($not)? has_attr)
            }
        )+
    };
    (@negate $has_attr:ident) => { $has_attr };
    (@negate $not:ident $has_attr:ident) => { ! $has_attr };
}

attribute_functions! {
    [creusot::no_translate]                  => is_no_translate
    [creusot::spec]                          => is_spec
    [creusot::spec::invariant]               => is_invariant
    [creusot::spec::variant]                 => is_variant
    [creusot::spec::variant::loop_]          => is_loop_variant
    [creusot::before_loop]                   => is_before_loop
    [creusot::spec::assert]                  => is_assertion
    [creusot::spec::snapshot]                => is_snapshot_closure
    [creusot::ghost]                         => is_ghost_closure
    [creusot::decl::logic]                   => is_logic
    [creusot::decl::logic::prophetic]        => is_prophetic
    [creusot::decl::predicate]               => is_predicate
    [creusot::decl::trusted]                 => is_trusted
    [creusot::decl::law]                     => is_law
    not [creusot::decl::no_trigger]          => should_replace_trigger
    [creusot::decl::open_inv_result]         => is_open_inv_result
    [creusot::extern_spec]                   => is_extern_spec
    [creusot::trusted_ignore_structural_inv] => is_ignore_structural_inv
    [creusot::trusted_is_tyinv_trivial_if_param_trivial] => is_tyinv_trivial_if_param_trivial
    [creusot::clause::variant]               => has_variant_clause
}

pub fn get_invariant_expl(tcx: TyCtxt, def_id: DefId) -> Option<String> {
    get_attr(tcx, tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "invariant"])
        .map(|a| a.value_str().map_or("expl:loop invariant".to_string(), |s| s.to_string()))
}

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

/// Get the string on the right of `creusot::builtin = ...`
pub(crate) fn get_builtin(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx, tcx.get_attrs_unchecked(def_id), &["creusot", "builtins"]).map(|a| {
        a.value_str().unwrap_or_else(|| {
            tcx.dcx().span_fatal(
                a.span,
                "Attribute `creusot::builtin` should be followed by a string.".to_string(),
            )
        })
    })
}

pub(crate) fn opacity_witness_name(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx, tcx.get_attrs_unchecked(def_id), &["creusot", "clause", "open"])
        .map(|a| a.value_str().expect("invalid creusot::clause::open"))
}

pub(crate) fn why3_attrs(tcx: TyCtxt, def_id: DefId) -> Vec<why3::declaration::Attribute> {
    get_attrs(tcx.get_attrs_unchecked(def_id), &["why3", "attr"])
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
    Some(
        get_attr(tcx, tcx.get_attrs_unchecked(def_id), &["creusot", "item"])?
            .value_str()
            .expect("invalid creusot::item attribute"),
    )
}

pub(crate) fn is_open_inv_param<'tcx>(tcx: TyCtxt<'tcx>, p: &Param) -> bool {
    let mut found = false;
    for a in &p.attrs {
        if a.is_doc_comment() {
            continue;
        }

        let item = a.get_normal_item();

        if item.path.segments.len() != 2 {
            continue;
        }

        if item
            .path
            .segments
            .iter()
            .zip(&["creusot", "open_inv"])
            .all(|(seg, s)| seg.ident.as_str() == *s)
        {
            if found {
                tcx.dcx().span_fatal(a.span, "Unexpected duplicate attribute.".to_string())
            }

            found = true
        }
    }

    return found;
}

fn get_attrs<'a>(attrs: &'a [Attribute], path: &[&str]) -> Vec<&'a Attribute> {
    let mut matched = Vec::new();

    for attr in attrs.iter() {
        if attr.is_doc_comment() {
            continue;
        }

        let item = attr.get_normal_item();

        if item.path.segments.len() != path.len() {
            continue;
        }

        let matches = item.path.segments.iter().zip(path).all(|(seg, s)| seg.name.as_str() == *s);

        if matches {
            matched.push(attr)
        }
    }
    matched
}

fn get_attr<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: &'a [Attribute],
    path: &[&str],
) -> Option<&'a Attribute> {
    let matched = get_attrs(attrs, path);
    match matched.len() {
        0 => return None,
        1 => return Some(matched[0]),
        _ => tcx.dcx().span_fatal(matched[0].span, "Unexpected duplicate attribute.".to_string()),
    }
}
