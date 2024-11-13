use crate::pretyping;
use proc_macro2::{Span, TokenStream};
use quote::{quote_spanned, ToTokens};
use syn::{
    parse_quote_spanned, spanned::Spanned, AttrStyle, Attribute, Error, Expr, ExprForLoop,
    ExprLoop, ExprWhile, Ident, Meta, Result,
};

#[derive(Debug)]
struct Invariant {
    span: Span,
    invariant: pearlite_syn::Term,
    expl: String,
}

impl ToTokens for Invariant {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.span;
        let expl = &self.expl;
        let inv_body = pretyping::encode_term(&self.invariant).unwrap_or_else(|e| e.into_tokens());

        tokens.extend(quote_spanned! {span=>
            #[allow(unused_must_use)]
            let _ = {
                #[creusot::no_translate]
                #[creusot::spec]
                #[creusot::spec::invariant = #expl]
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
        .extract_if(|attr| attr.path().get_ident().map(|i| i == "invariant").unwrap_or(false))
        .collect()
}

// Set the expl before pushing the invariant into the vector
fn parse_push_invariant(invariants: &mut Vec<Invariant>, invariant: TokenStream) -> Result<()> {
    let span = invariant.span();
    let invariant = syn::parse2(invariant)?;
    let expl = format! {"expl:loop invariant {}", invariants.len()};
    invariants.push(Invariant { span, invariant, expl });
    Ok(())
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

    let mut invariants = Vec::new();
    parse_push_invariant(&mut invariants, invariant)?;

    for attr in attrs {
        if let Meta::List(l) = attr.meta {
            parse_push_invariant(&mut invariants, l.tokens)?;
        } else {
            return Err(Error::new_spanned(attr, "expected #[invariant(...)]"));
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
            let sp = loop_.span;
            quote_spanned! {sp=> {
                #(#invariants)*
                #l
            }}
        }
    }
}

// Lowers for loops to `loop` and inserts the structural invariant that we get 'for free'
fn desugar_for(mut invariants: Vec<Invariant>, f: ExprForLoop) -> TokenStream {
    let lbl = f.label;
    let for_span = f.for_token.span;
    let pat = f.pat;
    let iter = f.expr;
    let body = f.body;
    let (outer, inner): (Vec<_>, _) =
        f.attrs.into_iter().partition(|f| matches!(f.style, AttrStyle::Outer));
    let produced = Ident::new("produced", for_span);
    let iter_old = Ident::new("iter_old", for_span);
    let it = Ident::new("iter", for_span);

    invariants.insert(
        0,
        Invariant {
            span: for_span,
            invariant: parse_quote_spanned! {for_span=> ::creusot_contracts::std::iter::Iterator::produces(#iter_old.inner(), #produced.inner(), #it) },
            expl: "expl:for invariant".to_string(),
        },
    );

    invariants.insert(
        0,
        Invariant {
            span: for_span,
            invariant: parse_quote_spanned! {for_span=> ::creusot_contracts::invariant::inv(#it) },
            expl: "expl:for invariant".to_string(),
        },
    );

    invariants.insert(
        0,
        Invariant {
            span: for_span,
            invariant: parse_quote_spanned! {for_span=> ::creusot_contracts::invariant::inv(*#produced) },
            expl: "expl:for invariant".to_string(),
        },
    );

    let elem = Ident::new("__creusot_proc_iter_elem", proc_macro::Span::def_site().into());

    quote_spanned! {for_span=> {
        let mut #it = ::std::iter::IntoIterator::into_iter(#iter);
        let #iter_old = snapshot! { #it };
        let mut #produced = snapshot! { ::creusot_contracts::logic::Seq::EMPTY };
        #(#invariants)*
        #(#outer)*
        #lbl
        loop {
            #(#inner)*
            match ::std::iter::Iterator::next(&mut #it) {
                Some(#elem) => {
                    #produced = snapshot! { #produced.inner().concat(::creusot_contracts::logic::Seq::singleton(#elem)) };
                    let #pat = #elem;
                    #body
                },
                None => break,
            }
        }
    } }
}
