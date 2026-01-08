//! Macros used to prove the internals of a function, or to create proof objects.

use crate::{
    common::{GhostClosuresVisitor, GhostLet, ghost_int_lit_suffix},
    creusot::pretyping,
};
use pearlite_syn::TBlock;
use proc_macro::TokenStream as TS1;
use quote::{ToTokens, quote};
use syn::{
    Block,
    parse::{self, Parse},
    parse_macro_input, token,
    visit_mut::VisitMut,
};

pub fn proof_assert(assertion: TS1) -> TS1 {
    let assert = parse_macro_input!(assertion as Assertion);
    let assert_body = pretyping::encode_block(&assert.0);

    TS1::from(quote! {
        {
            #[allow(let_underscore_drop)]
            let _ =
                #[creusot::no_translate]
                #[creusot::spec]
                #[creusot::spec::assert]
                || -> bool #assert_body;
        }
    })
}

pub fn snapshot(snapshot: TS1) -> TS1 {
    let snap = parse_macro_input!(snapshot as Assertion);
    let snap_body = pretyping::encode_block(&snap.0);

    TS1::from(quote! {
        ::creusot_std::__stubs::snapshot_from_fn(
            #[creusot::no_translate]
            #[creusot::spec]
            #[creusot::spec::snapshot]
            || #snap_body
        )
    })
}

pub fn ghost(body: TS1) -> TS1 {
    let group = proc_macro2::Group::new(proc_macro2::Delimiter::Brace, body.into());
    let body = ghost_int_lit_suffix(group.into_token_stream()).into();
    let mut body = parse_macro_input!(body as Block);
    GhostClosuresVisitor.visit_block_mut(&mut body);
    TS1::from(quote! {
        {
            #[creusot::ghost_block]
            {
                ::creusot_std::ghost::Ghost::new({ #body })
            }
        }
    })
}

pub fn ghost_let(body: TS1) -> TS1 {
    let body = ghost_int_lit_suffix(body.into()).into();
    let GhostLet { mutability, var, mut body } = parse_macro_input!(body);
    GhostClosuresVisitor.visit_expr_mut(&mut body);
    TS1::from(quote! {
        #[creusot::ghost_let]
        let __temp = #[creusot::ghost_block] ( #body );
        let #mutability #var = #[creusot::ghost_block] ::creusot_std::ghost::Ghost::new(__temp);
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
