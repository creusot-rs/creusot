use crate::common::FnOrMethod;
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream as TS2};
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    Pat, Path, Stmt, parse_macro_input, parse_quote, punctuated::Punctuated, spanned::Spanned as _,
    token::Comma,
};

pub(crate) fn refines(args: TS1, item: TS1) -> TS1 {
    // We parse the path to avoid injection attacks
    let path = parse_macro_input!(args as Path);
    let mut item = parse_macro_input!(item as FnOrMethod);
    let args: Punctuated<TS2, Comma> = item.sig.inputs.iter().map(|arg| match arg {
            syn::FnArg::Receiver(r) => {
                quote_spanned! { r.self_token.span => compile_error!("refines does not yet support self argument") }
            }
            syn::FnArg::Typed(p) => {
                match &*p.pat {
                    Pat::Ident(p) => p.ident.to_token_stream(),
                    _ => quote_spanned! { p.pat.span() => compile_error!("refines does not yet support pattern arguments") },
                }
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
