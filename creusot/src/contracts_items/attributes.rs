//! Defines all the internal creusot attributes.

use crate::ctx::{HasTyCtxt as _, TranslationCtx};
use rustc_ast::{
    LitKind, MetaItemInner, Param,
    token::TokenKind,
    tokenstream::{TokenStream, TokenTree},
};
use rustc_hir::{AttrArgs, Attribute, def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol};
use why3::{
    Name,
    declaration::{Attribute as WAttribute, Meta, MetaArg, MetaIdent},
};

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
                let has_attr = get_attr(tcx, tcx.get_all_attrs(def_id), path).is_some();
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
    [creusot::spec::erasure]                 => is_erasure
    [creusot::spec::invariant]               => is_invariant
    [creusot::spec::variant]                 => is_variant
    [creusot::spec::variant::loop_]          => is_loop_variant
    [creusot::before_loop]                   => is_before_loop
    [creusot::spec::assert]                  => is_assertion
    [creusot::spec::snapshot]                => is_snapshot_closure
    [creusot::logic_closure]                 => is_logic_closure // marks `forall`, `exists`, and mappings
    [creusot::decl::logic]                   => is_logic
    [creusot::decl::logic::prophetic]        => is_prophetic
    [creusot::decl::logic::sealed]           => is_sealed
    [creusot::decl::logic::law]              => is_law
    [creusot::decl::logic::inline]           => is_inline
    [creusot::decl::opaque]                  => is_opaque
    [creusot::decl::trusted]                 => is_trusted
    [creusot::decl::new_namespace]           => is_new_namespace
    not [creusot::decl::no_trigger]          => should_replace_trigger
    [creusot::decl::open_inv_result]         => is_open_inv_result
    [creusot::extern_spec]                   => is_extern_spec
    [creusot::trusted_ignore_structural_inv] => is_ignore_structural_inv
    [creusot::trusted_is_tyinv_trivial_if_param_trivial] => is_tyinv_trivial_if_param_trivial
    [creusot::clause::variant]               => has_variant_clause
    [creusot::clause::check_terminates]      => is_check_terminates
    [creusot::clause::check_ghost]           => is_check_ghost
    [creusot::bitwise]                       => is_bitwise
    [creusot::builtin_ascription]           => is_builtin_ascription
}

pub(crate) fn get_invariant_expl(tcx: TyCtxt, def_id: DefId) -> Option<String> {
    get_attr(tcx, tcx.get_all_attrs(def_id), &["creusot", "spec", "invariant"])
        .map(|a| a.value_str().map_or("expl:loop invariant".to_string(), |s| s.to_string()))
}

pub(crate) fn is_pearlite(tcx: TyCtxt, def_id: DefId) -> bool {
    is_spec(tcx, def_id)
        || is_logic_closure(tcx, def_id)
        || is_logic(tcx, def_id)
        || is_assertion(tcx, def_id)
        || is_snapshot_closure(tcx, def_id)
}

/// Get the string on the right of `creusot::builtin = ...`
pub(crate) fn get_builtin(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    if !matches!(
        tcx.def_kind(def_id),
        DefKind::Fn
            | DefKind::AssocFn
            | DefKind::AssocConst
            | DefKind::Const
            | DefKind::Struct
            | DefKind::Enum
            | DefKind::Union
    ) {
        return None;
    }

    let a = get_attr(tcx, tcx.get_all_attrs(def_id), &["creusot", "builtin"])?;
    Some(a.value_str().unwrap_or_else(|| {
        tcx.dcx().span_fatal(
            a.span(),
            "Attribute `creusot::builtin` should be followed by a string.".to_string(),
        )
    }))
}

pub(crate) fn get_intrinsic(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    Some(get_attr(tcx, tcx.get_all_attrs(def_id), &["creusot", "intrinsic"])?.value_str().unwrap())
}

pub(crate) fn opacity_witness_name(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx, tcx.get_all_attrs(def_id), &["creusot", "clause", "open"])
        .map(|a| a.value_str().expect("invalid creusot::clause::open"))
}

pub(crate) fn why3_attrs(tcx: TyCtxt, def_id: DefId) -> Vec<WAttribute> {
    get_attrs(tcx.get_all_attrs(def_id), &["creusot", "why3_attr"])
        .into_iter()
        .map(|a| WAttribute::Attr(a.value_str().unwrap().as_str().into()))
        .collect()
}

pub(crate) fn why3_metas(
    tcx: TyCtxt,
    def_id: DefId,
    ident: why3::Ident,
) -> impl Iterator<Item = Meta> {
    get_attrs(tcx.get_all_attrs(def_id), &["creusot", "why3_meta"]).into_iter().map(move |a| {
        let Some(items) = &a.meta_item_list() else {
            tcx.crash_and_error(
                a.span(),
                "Invalid creusot::why3_meta attribute: missing arguments".to_string(),
            )
        };
        tokenstream_to_meta(tcx, a.span(), ident, items.iter())
    })
}

fn tokenstream_to_meta<'a>(
    tcx: TyCtxt,
    span: Span,
    ident: why3::Ident,
    mut ts: impl Iterator<Item = &'a MetaItemInner>,
) -> Meta {
    let name = {
        let Some(LitKind::Str(name, _)) = ts.next().and_then(|item| item.lit().map(|lit| lit.kind))
        else {
            tcx.crash_and_error(span, "Invalid creusot::why3_meta attribute, missing name.\nExpected #[creusot::why3_meta(\"name\", ...)]")
        };
        MetaIdent(name.as_str().into())
    };
    let mut args = Vec::new();
    for token in ts {
        if let Some(name) = token.name() {
            if name.as_str() == "self" {
                args.push(MetaArg::Name(Name::local(ident)))
            } else {
                args.push(MetaArg::Keyword(name.as_str().into()));
            }
        } else if let Some(LitKind::Str(string, _)) = token.lit().map(|lit| &lit.kind) {
            args.push(MetaArg::String(string.as_str().into()))
        } else {
            tcx.crash_and_error(span, format!("Invalid creusot::why3_meta attribute argument: {token:?}\nExpected #[creusot::why3_meta(\"name\", arg1, ...)] where each arg is an identifier, self, or a string literal."));
        };
    }
    let args = args.into();
    Meta { name, args }
}

/// - `Some(Some(path))` if `#[creusot::spec::erasure(path)]`
/// - `Some(None)` if `#[creusot::spec::erasure]`
/// - `None` if no matching attribute
pub(crate) fn get_erasure(tcx: TyCtxt, def_id: DefId) -> Option<Option<Vec<Symbol>>> {
    let attr = get_attrs(tcx.get_all_attrs(def_id), &["creusot", "spec", "erasure"]).pop()?;
    let Attribute::Unparsed(attr) = attr else { unreachable!() };
    match &attr.args {
        AttrArgs::Delimited(args) => Some(Some(tokenstream_to_path(tcx, def_id, &args.tokens))),
        AttrArgs::Empty => Some(None),
        _ => tcx.crash_and_error(tcx.def_span(def_id), "Bad #[erasure] attribute"),
    }
}

fn tokenstream_to_path(tcx: TyCtxt, def_id: DefId, tokens: &TokenStream) -> Vec<Symbol> {
    let crash = || tcx.crash_and_error(tcx.def_span(def_id), "Bad #[erasure] attribute");
    tokens
        .iter()
        .filter_map(|token| {
            let TokenTree::Token(token, _) = token else { crash() };
            match token.kind {
                TokenKind::PathSep => None,
                TokenKind::Ident(name, _) => Some(name),
                _ => crash(),
            }
        })
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
    get_attrs(tcx.get_all_attrs(def_id), &["creusot", "clause", clause])
        .into_iter()
        .rev()
        .map(|a| &a.get_normal_item().args)
}

pub(crate) fn get_creusot_item(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    Some(
        get_attr(tcx, tcx.get_all_attrs(def_id), &["creusot", "item"])?
            .value_str()
            .expect("invalid creusot::item attribute"),
    )
}

pub(crate) fn is_open_inv_param(tcx: TyCtxt, p: &Param) -> bool {
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

    found
}

/// If a function is annotated with `#[has_logical_alias(f)]`, return the [`DefId`] of `f`.
pub(crate) fn function_has_logical_alias(
    ctx: &mut TranslationCtx,
    def_id: DefId,
) -> Option<(Span, DefId)> {
    let attrs = get_attrs(ctx.get_all_attrs(def_id), &["creusot", "decl", "logical_alias_path"]);
    let attr = match attrs.as_slice() {
        [] => return None,
        [a] => a,
        _ => {
            ctx.dcx().span_err(
                attrs.iter().map(|attr| attr.span()).collect::<Vec<_>>(),
                "A function cannot have multiple logical aliases",
            );
            return None;
        }
    };
    let symbol = match &attr.get_normal_item().args {
        AttrArgs::Eq { expr, .. } => expr.symbol,
        _ => unreachable!(),
    };
    // the `ensures(result == f(args))` clause
    let ensures_def_id = ctx.creusot_item(symbol).unwrap();
    let ensures_body =
        ctx.term(ensures_def_id).expect("no ensures clause associated with this alias");
    match &ensures_body.1.kind {
        crate::translation::pearlite::TermKind::Binary { rhs, .. } => match &rhs.kind {
            crate::translation::pearlite::TermKind::Call { id, .. } => Some((attr.span(), *id)),
            _ => unreachable!("this should be a function call"),
        },
        _ => unreachable!("this should be an equality"),
    }
}

fn get_attrs<'a>(attrs: &'a [Attribute], path: &[&str]) -> Vec<&'a Attribute> {
    let mut matched = Vec::new();

    for attr in attrs.iter() {
        if attr.is_doc_comment() {
            continue;
        }

        let Attribute::Unparsed(item) = attr else { continue };

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

fn get_attr<'a>(tcx: TyCtxt, attrs: &'a [Attribute], path: &[&str]) -> Option<&'a Attribute> {
    let matched = get_attrs(attrs, path);
    match matched.len() {
        0 => None,
        1 => Some(matched[0]),
        _ => tcx.dcx().span_fatal(matched[0].span(), "Unexpected duplicate attribute.".to_string()),
    }
}
