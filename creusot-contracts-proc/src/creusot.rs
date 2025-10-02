mod derive;
pub(crate) mod doc;
mod erasure;
mod extern_spec;
mod invariant;
mod logic;
pub(crate) mod pretyping;
mod proof;
mod specs;

pub(crate) use self::{
    derive::*,
    erasure::erasure,
    extern_spec::extern_spec,
    logic::{logic, pearlite},
    proof::{ghost, ghost_let, invariant, proof_assert, snapshot},
    specs::{bitwise_proof, check, ensures, has_logical_alias, maintains, requires, variant},
};

use crate::common::{ContractSubject, FnOrMethod};
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    Error, FnArg, Ident, LitStr, Macro, Result, Token,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
};

pub fn open_inv_result(_: TS1, tokens: TS1) -> TS1 {
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::open_inv_result]
        #tokens
    })
}

pub fn trusted(_: TS1, tokens: TS1) -> TS1 {
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::trusted]
        #[allow(creusot::experimental)]
        #tokens
    })
}

pub fn opaque(_: TS1, tokens: TS1) -> TS1 {
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::opaque]
        #tokens
    })
}

struct Builtin {
    str: TokenStream,
    ascription: bool,
}

impl Parse for Builtin {
    fn parse(input: ParseStream) -> Result<Self> {
        let str = if input.fork().parse::<Macro>().is_ok() {
            let mac: Macro = input.parse().unwrap();
            quote! { #mac }
        } else {
            let str: LitStr = input.parse()?;
            quote! { #str }
        };

        if input.peek(Token![,]) {
            let _: Token![,] = input.parse()?;
            let asc: Ident = input.parse()?;
            if asc != "ascription" {
                Result::Err(Error::new(
                    asc.span(),
                    "The second parameter of #[builtin], if present, should be `ascription`.",
                ))?
            }
            Ok(Builtin { str, ascription: true })
        } else {
            Ok(Builtin { str, ascription: false })
        }
    }
}

pub fn builtin(params: TS1, tokens: TS1) -> TS1 {
    let builtin = parse_macro_input!(params as Builtin);
    let asc = if builtin.ascription {
        quote! { #[creusot::builtin_ascription] }
    } else {
        quote! {}
    };
    let str = builtin.str;

    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::builtin = #str]
        #asc
        #tokens
    })
}

pub fn intrinsic(params: TS1, tokens: TS1) -> TS1 {
    let params = TokenStream::from(params);
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::intrinsic = #params]
        #tokens
    })
}

pub fn declare_namespace(namespace: TS1) -> TS1 {
    let ident = parse_macro_input!(namespace as Ident);
    quote! {
        #[trusted]
        #[logic(opaque)]
        #[creusot::decl::new_namespace]
        #[allow(nonstandard_style)]
        pub fn #ident() -> ::creusot_contracts::ghost::local_invariant::Namespace {
            dead
        }
    }
    .into()
}

impl FnOrMethod {
    fn is_trait_signature(&self) -> bool {
        self.semi_token.is_some()
    }
}

impl ContractSubject {
    fn name(&self) -> String {
        match self {
            ContractSubject::FnOrMethod(tr) => tr.sig.ident.to_string(),
            ContractSubject::Closure(_) => "closure".to_string(),
        }
    }

    fn mark_unused(&mut self) {
        if let ContractSubject::FnOrMethod(sig) = self {
            for arg in sig.sig.inputs.iter_mut() {
                let attrs = match arg {
                    FnArg::Receiver(r) => &mut r.attrs,
                    FnArg::Typed(r) => &mut r.attrs,
                };
                attrs.push(parse_quote! { #[allow(unused)]});
            }
        }
    }
}

fn generate_unique_ident(prefix: &str, span: Span) -> Ident {
    Ident::new(&generate_unique_string(prefix), span)
}

fn generate_unique_string(prefix: &str) -> String {
    let uuid = uuid::Uuid::new_v4();
    format!("{}_{}", prefix, uuid).replace('-', "_")
}

// Utilities for debugging

#[allow(unused)]
pub(crate) fn dump_tokens(tokens: &TokenStream) {
    eprintln! {"{}", tokens};
    eprint_tokens(tokens);
}

pub(crate) fn eprint_tokens(tokens: &TokenStream) {
    for t in tokens.clone().into_iter() {
        if let proc_macro2::TokenTree::Group(g) = t {
            eprintln! {"Group {:?} {:?}", g.delimiter(), pretty_span(&g.span())};
            eprint_tokens(&g.stream());
        } else {
            eprintln! {"{} {:?}", t, pretty_span(&t.span())};
        }
    }
}

pub(crate) fn pretty_span(span: &Span) -> String {
    let start = span.start();
    let end = span.end();
    format! {"{:?}:{:?}:{:?}-{:?}:{:?}", span.unwrap().file(), start.line, start.column, end.line, end.column}
}
