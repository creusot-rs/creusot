use crate::pretyping;
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    parse_quote, spanned::Spanned, AttrStyle, Attribute, Error, Expr, ExprForLoop, ExprLoop,
    ExprWhile, Ident, Meta, Result,
};

#[derive(Debug)]
struct Invariant {
    span: Span,
    invariant: pearlite_syn::Term,
}

impl syn::parse::Parse for Invariant {
    fn parse(tokens: syn::parse::ParseStream) -> Result<Self> {
        let span = tokens.span();
        let invariant = tokens.parse()?;

        Ok(Invariant { span, invariant })
    }
}

impl ToTokens for Invariant {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let term = &self.invariant;

        // TODO: Move out of `ToTokens`
        let s = self.span;
        let inv_body = pretyping::encode_term(term).unwrap();
        let inv_body = quote_spanned! {s=> #inv_body};

        tokens.extend(quote_spanned! {s=>
            #[allow(unused_must_use)]
            let _ = {
                #[creusot::no_translate]
                #[creusot::spec]
                #[creusot::spec::invariant]
                ||{ #inv_body }
            };
        })
    }
}

enum LoopKind {
    For(ExprForLoop),
    While(ExprWhile),
    Loop(ExprLoop),
}

pub struct Loop {
    span: Span,
    invariants: Vec<Invariant>,
    kind: LoopKind,
}

fn filter_invariants(attrs: &mut Vec<Attribute>) -> Vec<Attribute> {
    attrs
        .drain_filter(|attr| attr.path().get_ident().map(|i| i == "invariant").unwrap_or(false))
        .collect()
}

pub fn parse(invariant: TokenStream, loopb: TokenStream) -> Result<Loop> {
    let body: Expr = syn::parse2(loopb)?;
    let span = body.span();
    let (attrs, lkind) = match body {
        Expr::ForLoop(mut floop) => (filter_invariants(&mut floop.attrs), LoopKind::For(floop)),
        Expr::While(mut wloop) => (filter_invariants(&mut wloop.attrs), LoopKind::While(wloop)),
        Expr::Loop(mut lloop) => (filter_invariants(&mut lloop.attrs), LoopKind::Loop(lloop)),
        _ => {
            return Err(Error::new_spanned(
                body,
                "invariants must be attached to either a `for`, `loop` or `while`",
            ))
        }
    };

    let mut invariants = vec![syn::parse2(invariant)?];

    for attr in attrs {
        if let Meta::List(l) = attr.meta {
            invariants.push(syn::parse2(l.tokens)?);
        } else {
            panic!()
        }
    }

    Ok(Loop { invariants, span, kind: lkind })
}

pub fn lower(loop_: Loop) -> TokenStream {
    let invariants = loop_.invariants;
    match loop_.kind {
        LoopKind::For(floop) => desugar_for(invariants, floop),
        LoopKind::While(l) => {
            let mut tokens = TokenStream::new();
            for i in invariants {
                i.to_tokens(&mut tokens);
            }
            let sp = loop_.span;
            quote_spanned! {sp=>{
                #tokens
                #l
            }}
        }
        LoopKind::Loop(l) => {
            quote! {{
                #(#invariants;)*
                #l
            }}
        }
    }
}

// Lowers for loops to `loop` and inserts the structural invariant that we get 'for free'
fn desugar_for(mut invariants: Vec<Invariant>, f: ExprForLoop) -> TokenStream {
    let lbl = f.label;
    let pat = f.pat;
    let iter = f.expr;
    let body = f.body;
    let (outer, inner): (Vec<_>, _) =
        f.attrs.into_iter().partition(|f| matches!(f.style, AttrStyle::Outer));
    let produced = Ident::new("produced", Span::call_site());
    let iter_old = Ident::new("iter_old", Span::call_site());
    let it = Ident::new("iter", Span::call_site());

    invariants.insert(
        0,
        Invariant {
            span: Span::call_site(),
            invariant: parse_quote! { ::creusot_contracts::std::iter::Iterator::produces(#iter_old.inner(), #produced.inner(), #it) },
        },
    );

    invariants.insert(
        0,
        Invariant {
            span: Span::call_site(),
            invariant: parse_quote! { ::creusot_contracts::invariant::Invariant::invariant(#it) },
        },
    );

    let elem = Ident::new("__creusot_proc_iter_elem", proc_macro::Span::def_site().into());

    quote! { {
        let mut #it = ::std::iter::IntoIterator::into_iter(#iter);
        let #iter_old = ghost! { #it };
        let mut #produced = ghost! { ::creusot_contracts::logic::Seq::EMPTY };
        #(#invariants;)*
        #(#outer)*
        #lbl
        loop {
            #(#inner)*
            match ::std::iter::Iterator::next(&mut #it) {
                Some(#elem) => {
                    #produced = ghost! { #produced.inner().concat(::creusot_contracts::logic::Seq::singleton(#elem)) };
                    let #pat = #elem;
                    #body
                },
                None => break,
            }
        }
    } }
}
