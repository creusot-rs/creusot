#![feature(stmt_expr_attributes)]
#![feature(register_tool)]
#![register_tool(creusot)]

extern crate proc_macro;

use syn::*;

use proc_macro::TokenStream as TS1;
use quote::quote;

#[proc_macro_attribute]
pub fn requires(attr: TS1, tokens: TS1) -> TS1 {
    let p: syn::Term = parse_macro_input!(attr);

    let f: ItemFn = parse_macro_input!(tokens);

    let req_toks = format!("{}", quote! {#p});
    // TODO: Parse and pass down all the function's arguments.
    TS1::from(quote! {
      #[creusot::spec::requires=#req_toks]
      #f
    })
}

#[proc_macro_attribute]
pub fn ensures(attr: TS1, tokens: TS1) -> TS1 {
    let p: syn::Term = parse_macro_input!(attr);
    let f: ItemFn = parse_macro_input!(tokens);

    let req_toks = format!("{}", quote! {#p});
    // TODO: Parse and pass down all the function's arguments.
    TS1::from(quote! {
      #[creusot::spec::ensures=#req_toks]
      #f
    })
}

#[proc_macro_attribute]
pub fn variant(attr: TS1, tokens: TS1) -> TS1 {
    let p: syn::Term = parse_macro_input!(attr);
    let f: ItemFn = parse_macro_input!(tokens);
    let variant_tokens = format!("{}", quote! {#p});

    TS1::from(quote! {
      #[creusot::spec::variant=#variant_tokens]
      #f
    })
}

struct Invariant {
    name: syn::Ident,
    invariant: syn::Term,
}

impl syn::parse::Parse for Invariant {
    fn parse(tokens: syn::parse::ParseStream) -> Result<Self> {
        let name = tokens.parse()?;
        let _: Token![,] = tokens.parse()?;
        let invariant = tokens.parse()?;

        Ok(Invariant { name, invariant })
    }
}
#[proc_macro_attribute]
pub fn invariant(invariant: TS1, loopb: TS1) -> TS1 {
    let inv: Invariant = parse_macro_input!(invariant);
    let term = inv.invariant;
    let inv_toks = format!("{}", quote! {#term});
    let loopb = proc_macro2::TokenStream::from(loopb);
    let invariant_name = inv.name;
    TS1::from(quote! {
        {
            #[allow(unused_must_use)]
            let _ = {
                #[creusot::spec::invariant::#invariant_name=#inv_toks]
                ||{}
            };
            #loopb
        }
    })
}

struct LogicItem {
    vis: Visibility,
    attrs: Vec<Attribute>,
    sig: Signature,
    body: Term,
}

impl syn::parse::Parse for LogicItem {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = Attribute::parse_outer(input)?;
        let vis = input.parse()?;
        let sig = input.parse()?;
        let body;
        braced!(body in input);
        let body = body.parse()?;

        Ok(LogicItem { vis, attrs, sig, body })
    }
}

#[proc_macro]
pub fn logic(body: TS1) -> TS1 {
    let log: LogicItem = parse_macro_input!(body);
    let term = log.body;
    let term = format!("{}", quote! {#term});
    let vis = log.vis;
    let sig = log.sig;
    let attrs = log.attrs;
    TS1::from(quote! {
        #[creusot::spec::logic=#term]
        #(#attrs)*
        #vis #sig {
            std::process::abort()
        }
    })
}
