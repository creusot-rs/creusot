//! Macros used to prove the internals of a function, or to create proof objects.

use crate::{
    common::{GhostLet, ghost_int_lit_suffix},
    creusot::{invariant::desugar_invariant, pretyping},
};
use pearlite_syn::{Binder, Term, TermBlock, TermStmt};
use proc_macro::TokenStream as TS1;
use proc_macro2::{Delimiter, Group, Span, TokenStream as TS2};
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    Attribute, Block, ExprClosure, Token,
    parse::{self, Parse},
    parse_macro_input, parse_quote, token,
    visit_mut::{VisitMut, visit_expr_closure_mut},
};

pub fn proof_assert(assertion: TS1) -> TS1 {
    proof_assert_(assertion.into(), false)
}

pub fn proof_assert_(assertion: TS1, trusted: bool) -> TS1 {
    let assert = parse_macro_input!(assertion as Assertion);
    let assert = assert.encode();
    let attr = if trusted {
        quote! { #[creusot::decl::trusted] }
    } else {
        quote! {}
    };
    TS1::from(quote! {
        {
            #[allow(let_underscore_drop)]
            let _ =
                #[creusot::no_translate]
                #[creusot::spec]
                #[creusot::spec::assert]
                #attr
                #assert;
        }
    })
}

pub fn snapshot(snapshot: TS1) -> TS1 {
    let snap = parse_macro_input!(snapshot as TermStmts);
    let snap_body = pretyping::encode_stmts(&snap.stmts, snap.span);

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
    let group = Group::new(Delimiter::Brace, body.into());
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
    desugar_invariant(invariant.into(), tokens.into())
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

// FIXME: merge with TermContract (which doesn't allow statements before the assertion)
enum Assertion {
    /// A plain assertion, possibly preceded by statements
    Block { stmts: Vec<TermStmt>, span: Span },
    /// An assertion that binds the proof mode
    Binder { binder: Binder, term: Term, span: Span },
}

impl Parse for Assertion {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let span = input.span();
        if input.peek(Token![|]) {
            let binder = input.parse()?;
            let term = input.parse()?;
            Ok(Assertion::Binder { binder, term, span })
        } else {
            let stmts = input.call(TermBlock::parse_within)?;
            Ok(Assertion::Block { stmts, span })
        }
    }
}

impl Assertion {
    fn encode(&self) -> TS2 {
        match self {
            &Assertion::Block { ref stmts, span } => {
                let body = pretyping::encode_stmts(stmts, span);
                quote_spanned! {span=> |_: ::creusot_std::mode::Mode| -> bool { #body } }
            }
            &Assertion::Binder { ref binder, ref term, span } => {
                let body = pretyping::encode_term(term);
                quote_spanned! {span=> #binder -> bool { #body }}
            }
        }
    }
}

struct TermStmts {
    stmts: Vec<TermStmt>,
    span: Span,
}

impl Parse for TermStmts {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let span = input.span();
        let stmts = input.call(TermBlock::parse_within)?;
        Ok(TermStmts { stmts, span })
    }
}

pub(crate) struct GhostClosuresVisitor;

impl VisitMut for GhostClosuresVisitor {
    fn visit_expr_closure_mut(&mut self, i: &mut ExprClosure) {
        let attr: Attribute = parse_quote!(#[check(ghost)]);
        i.attrs.push(attr);
        visit_expr_closure_mut(self, i);
    }
}
