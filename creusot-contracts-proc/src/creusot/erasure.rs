use super::doc;
use crate::common::FnOrMethod;
use proc_macro::{Diagnostic, Level, TokenStream as TS1};
use proc_macro2::TokenStream as TS2;
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    ExprPath, Pat, PathArguments, Stmt, Type, parse_macro_input, parse_quote,
    punctuated::Punctuated, spanned::Spanned as _, token::Comma,
};

pub(crate) fn erasure(path: TS1, item: TS1) -> TS1 {
    let path = parse_macro_input!(path as ExprPath);
    let mut item = parse_macro_input!(item as FnOrMethod);
    let args: Punctuated<TS2, Comma> = item.sig.inputs.iter().filter_map(|arg| match arg {
            syn::FnArg::Receiver(r) => {
                Some(r.self_token.to_token_stream())
            }
            syn::FnArg::Typed(p) => {
                if is_ghost_ty(&p.ty) { return None }
                Some(match &*p.pat {
                    Pat::Ident(p) => p.ident.to_token_stream(),
                    _ => quote_spanned! { p.pat.span() => compile_error!("#[erasure] does not yet support pattern arguments") },
                })
            }
        }).collect();
    let erasure_gadget: Stmt = parse_quote! {
        #[allow(let_underscore_drop)]
        let _ =
            #[creusot::no_translate]
            #[creusot::spec::erasure]
            || #path(#args);
    };
    item.body.as_mut().unwrap().stmts.insert(0, erasure_gadget);
    let doc = doc::document_spec("erasure", doc::LogicBody::Some(TS1::from(quote!(#path))));
    insert_doc(item, doc)
}

fn insert_doc(item: FnOrMethod, doc: TS2) -> TS1 {
    let FnOrMethod { attrs, defaultness, visibility, sig, body, semi_token } = item;
    TS1::from(quote! {
        #(#attrs)* #doc
        #defaultness #visibility #sig #body #semi_token
    })
}

fn is_ghost_ty(ty: &Type) -> bool {
    let Type::Path(ty) = ty else { return false };
    let None = ty.qself else { return false };
    let Some(segment) = ty.path.segments.last() else { return false };
    let PathArguments::AngleBracketed(_) = segment.arguments else { return false };
    let name = segment.ident.to_string();
    if name == "Ghost" {
        if ty.path.segments.len() != 1 || ty.path.leading_colon.is_some() {
            warn_unerased_ghost(ty.span().unwrap());
            return false;
        }
        true
    } else if name == "Snapshot" {
        if ty.path.segments.len() != 1 || ty.path.leading_colon.is_some() {
            warn_unerased_snapshot(ty.span().unwrap());
            return false;
        }
        true
    } else {
        false
    }
}

fn warn_unerased_ghost(span: proc_macro::Span) {
    Diagnostic::spanned(span, Level::Warning, "`#[erasure]` won't erase this `Ghost` argument")
        .note("only arguments whose type is unqualified `Ghost<_>` are erased")
        .note("if this `Ghost` is not referring to `creusot_contracts::Ghost`, rename your `Ghost` to a different name to silence this warning")
        .emit();
}

fn warn_unerased_snapshot(span: proc_macro::Span) {
    Diagnostic::spanned(span, Level::Warning, "`#[erasure]` won't erase this `Snapshot` argument")
        .note("only arguments whose type is unqualified `Snapshot<_>` are erased")
        .note("if this `Snapshot` is not referring to `creusot_contracts::Snapshot`, rename your `Snapshot` to a different name to silence this warning")
        .emit();
}
