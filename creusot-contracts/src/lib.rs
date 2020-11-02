#![feature(stmt_expr_attributes)]
#![feature(register_tool)]
#![register_tool(creusot)]

extern crate proc_macro;

use proc_macro::TokenStream;

use syn::parse_macro_input;

use quote::quote;

#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

struct Assert(syn::Expr);

impl syn::parse::Parse for Assert {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let e = input.parse()?;

        Ok(Assert(e))
    }
}

#[proc_macro]
pub fn assert(tokens: TokenStream) -> TokenStream {
    let inp: Assert = parse_macro_input!(tokens);
    let assert_id = uuid::Uuid::new_v4().to_string();
    let assert_exp = inp.0;

    TokenStream::from(quote! {
      #[allow(unused_must_use, unused_variables)]
      #[creusot::ghost]
      #[creusot::assert_id = #assert_id]
      ||{ #assert_exp }
    })
}

struct AssertEq(syn::Expr, syn::Expr);

impl syn::parse::Parse for AssertEq {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let e1 = input.parse()?;
        let e2 = input.parse()?;

        Ok(AssertEq(e1, e2))
    }
}

#[proc_macro]
pub fn assert_eq(tokens: TokenStream) -> TokenStream {
    let inp: AssertEq = parse_macro_input!(tokens);
    let assert_id = uuid::Uuid::new_v4().to_string();
    let left_exp = inp.0;
    let right_exp = inp.1;

    TokenStream::from(quote! {
      #[allow(unused_must_use, unused_variables)]
      #[creusot::ghost]
      #[creusot::assert_id = #assert_id]
      ||{ #left_exp == #right_exp }
    })
}
