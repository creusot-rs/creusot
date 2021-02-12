#![feature(stmt_expr_attributes)]
#![feature(register_tool)]
#![register_tool(creusot)]

extern crate proc_macro;

use syn::*;

use quote::quote;

#[proc_macro_attribute]
pub fn requires(attr: proc_macro::TokenStream, tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let p: syn::Term = parse_macro_input!(attr);

    let f: ItemFn = parse_macro_input!(tokens);

    let req_toks = format!("{}", quote! {#p});
    // TODO: Parse and pass down all the function's arguments.
    proc_macro::TokenStream::from(quote! {
      #[creusot::spec::requires=#req_toks]
      #f
    })
}

#[proc_macro_attribute]
pub fn ensures(attr: proc_macro::TokenStream, tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let p: syn::Term = parse_macro_input!(attr);

    let f: ItemFn = parse_macro_input!(tokens);

    let req_toks = format!("{}", quote! {#p});
    // TODO: Parse and pass down all the function's arguments.
    proc_macro::TokenStream::from(quote! {
      #[creusot::spec::ensures=#req_toks]
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
#[proc_macro]
pub fn invariant(invariant: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let inv: Invariant = parse_macro_input!(invariant);

    let term = inv.invariant;
    let inv_toks = format!("{}", quote! {#term});

    let invariant_name = inv.name;
    proc_macro::TokenStream::from(quote! {
        #[creusot::spec::invariant::#invariant_name=#inv_toks]
        ||{};
    })
}
