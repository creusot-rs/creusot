//! Macros used to prove the internals of a function, or to create proof objects.

use super::pretyping;
use pearlite_syn::TBlock;
use proc_macro::TokenStream as TS1;
use quote::quote;
use syn::{
    parse::{self, Parse},
    parse_macro_input, token,
};

pub fn proof_assert(assertion: TS1) -> TS1 {
    let assert = parse_macro_input!(assertion as Assertion);
    let assert_body = pretyping::encode_block(&assert.0);

    TS1::from(quote! {
        {
            #[allow(let_underscore_drop)]
            let _ = {
                #[creusot::no_translate]
                #[creusot::spec]
                #[creusot::spec::assert]
                #[allow(unused_braces)]
                || -> bool #assert_body
            };
        }
    })
}

pub fn snapshot(assertion: TS1) -> TS1 {
    let assert = parse_macro_input!(assertion as Assertion);
    let assert_body = pretyping::encode_block(&assert.0);

    TS1::from(quote! {
        ::creusot_contracts::__stubs::snapshot_from_fn(
            #[creusot::no_translate]
            #[creusot::spec]
            #[creusot::spec::snapshot]
            || ::creusot_contracts::snapshot::Snapshot::new (#[allow(unused_braces)] #assert_body)
        )
    })
}

pub fn ghost(body: TS1) -> TS1 {
    let body = proc_macro2::TokenStream::from(crate::ghost::ghost_preprocess(body));
    TS1::from(quote! {
        {
            #[creusot::ghost_block]
            {
                ::creusot_contracts::ghost::Ghost::new({ #body })
            }
        }
    })
}

struct GhostLet {
    mutability: Option<syn::Token![mut]>,
    var: syn::Ident,
    body: syn::Expr,
}

impl syn::parse::Parse for GhostLet {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let mutability = input.parse()?;
        let var = input.parse()?;
        let _: syn::Token![=] = input.parse()?;
        let body = input.parse()?;
        Ok(Self { mutability, var, body })
    }
}

pub fn ghost_let(body: TS1) -> TS1 {
    let body = crate::ghost::ghost_preprocess(body);
    let GhostLet { mutability, var, body } = parse_macro_input!(body as GhostLet);
    TS1::from(quote! {
        #[creusot::ghost_let]
        let __temp = #[creusot::ghost_block] ( #body );
        let #mutability #var = #[creusot::ghost_block] ::creusot_contracts::ghost::Ghost::new(__temp);
    })
}

pub fn invariant(invariant: TS1, tokens: TS1) -> TS1 {
    super::invariant::desugar_invariant(invariant.into(), tokens.into())
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

/// An assertion is a sequence of statements (`Vec<Stmt>`).
/// The `brace_token` is artificially generated from the span of the body.
struct Assertion(TBlock);

impl Parse for Assertion {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let brace_token = token::Brace(input.span());
        let stmts = input.call(TBlock::parse_within)?;
        Ok(Assertion(TBlock { brace_token, stmts }))
    }
}
