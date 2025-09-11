use crate::common::FnOrMethod;
use proc_macro::{Diagnostic, Level, TokenStream as TS1};
use proc_macro2::TokenStream as TS2;
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    ExprPath, Pat, PathArguments, Stmt, Type, parse_macro_input, parse_quote,
    punctuated::Punctuated, spanned::Spanned as _, token::Comma,
};

pub(crate) fn refines(path: TS1, item: TS1) -> TS1 {
    // We parse the path to avoid injection attacks
    let path = parse_macro_input!(path as ExprPath);
    let mut item = parse_macro_input!(item as FnOrMethod);
    let args: Punctuated<TS2, Comma> = item.sig.inputs.iter().filter_map(|arg| match arg {
            syn::FnArg::Receiver(r) => {
                Some(quote_spanned! { r.self_token.span => compile_error!("#[refines] does not yet support self argument") })
            }
            syn::FnArg::Typed(p) => {
                if is_ghost_ty(&p.ty) { return None }
                Some(match &*p.pat {
                    Pat::Ident(p) => p.ident.to_token_stream(),
                    _ => quote_spanned! { p.pat.span() => compile_error!("#[refines] does not yet support pattern arguments") },
                })
            }
        }).collect();
    let refines_gadget: Stmt = parse_quote! {
        #[allow(let_underscore_drop)]
        let _ =
            #[creusot::no_translate]
            #[creusot::spec::refines]
            || #path(#args);
    };
    item.body.as_mut().unwrap().stmts.insert(0, refines_gadget);
    TS1::from(quote! {
        #item
    })
}

fn is_ghost_ty(ty: &Type) -> bool {
    let Type::Path(ty) = ty else { return false };
    let None = ty.qself else { return false };
    let Some(segment) = ty.path.segments.last() else { return false };
    let PathArguments::AngleBracketed(_) = segment.arguments else { return false };
    if segment.ident.to_string() != "Ghost" {
        return false;
    };
    if ty.path.segments.len() != 1 || ty.path.leading_colon.is_some() {
        Diagnostic::spanned(ty.span().unwrap(), Level::Warning, "#[refines] won't erase this Ghost argument")
            .note("only arguments whose type is unqualified `Ghost<_>` are erased")
            .note("if this `Ghost` is not referring to `creusot_contracts::Ghost`, rename your Ghost to a different name to silence this warning")
            .emit();
        return false;
    }
    true
}
