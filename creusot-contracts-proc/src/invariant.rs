use crate::pretyping;
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    parse_quote_spanned, spanned::Spanned, token::Brace, AttrStyle, Attribute, Block, Error, Expr,
    ExprForLoop, ExprLoop, ExprWhile, Ident, ItemFn, Meta, Result, Stmt, Token,
};

#[derive(Debug, Clone, Copy)]
enum InvariantKind {
    ForInvariant,
    LoopInvariant(Option<usize>),
}
use InvariantKind::*;

#[derive(Debug)]
enum Tag {
    Invariant(InvariantKind),
    Variant,
}

// Represents both invariants and variants
#[derive(Debug)]
struct Invariant {
    tag: Tag,
    span: Span,
    term: pearlite_syn::Term,
}

impl ToTokens for Invariant {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.span;
        let term = pretyping::encode_term(&self.term).unwrap_or_else(|e| e.into_tokens());
        let spec_closure = match self.tag {
            Tag::Invariant(kind) => {
                let expl = match kind {
                    LoopInvariant(Some(n)) => format!("expl:loop invariant #{}", n),
                    LoopInvariant(None) => "expl:loop invariant".to_string(),
                    ForInvariant => "expl:for invariant".to_string(),
                };
                quote_spanned! {span=>
                  #[creusot::spec::invariant = #expl]
                  ||{ #term }
                }
            }
            Tag::Variant => quote_spanned! {span=>
              #[creusot::spec::variant::loop_]
              ||{ ::creusot_contracts::__stubs::variant_check(#term) }
            },
        };
        tokens.extend(quote_spanned! {span=>
            #[allow(unused_must_use)]
            let _ =
                #[creusot::no_translate]
                #[creusot::spec]
                #spec_closure;
        })
    }
}

pub fn desugar_invariant(invariant0: TokenStream, expr: TokenStream) -> Result<TokenStream> {
    desugar(Tag::Invariant(LoopInvariant(Some(0))), invariant0, expr)
}

fn desugar(tag: Tag, invariant0: TokenStream, expr: TokenStream) -> Result<TokenStream> {
    let expr: Expr = syn::parse2(expr)?;
    let invariants = |attrs| filter_invariants(tag, invariant0, attrs);
    match expr {
        Expr::ForLoop(mut expr) => Ok(desugar_for(invariants(&mut expr.attrs)?, expr)),
        Expr::While(mut expr) => Ok(desugar_while(invariants(&mut expr.attrs)?, expr)),
        Expr::Loop(mut expr) => Ok(desugar_loop(invariants(&mut expr.attrs)?, expr)),
        _ => {
            return Err(Error::new_spanned(
                expr,
                "invariants must be attached to either a `for`, `loop` or `while`",
            ))
        }
    }
}

// Set the expl before pushing the invariant into the vector
fn parse_push_invariant(
    invariants: &mut Vec<Invariant>,
    tag: Tag,
    term: TokenStream,
) -> Result<()> {
    let span = term.span();
    let term = syn::parse2(term)?;
    invariants.push(Invariant { tag, span, term });
    Ok(())
}

fn filter_invariants(
    tag: Tag,
    invariant: TokenStream,
    attrs: &mut Vec<Attribute>,
) -> Result<Vec<Invariant>> {
    let mut n_invariants = if let Tag::Variant = &tag { 0 } else { 1 };
    let mut invariants = Vec::new();
    parse_push_invariant(&mut invariants, tag, invariant)?;

    let attrs = attrs.extract_if(|attr| {
        attr.path().get_ident().map_or(false, |i| i == "invariant" || i == "variant")
    });
    for attr in attrs {
        let i = if attr.path().get_ident().map(|i| i == "invariant").unwrap_or(false) {
            n_invariants += 1;
            Tag::Invariant(LoopInvariant(Some(n_invariants - 1)))
        } else {
            Tag::Variant
        };
        if let Meta::List(l) = attr.meta {
            parse_push_invariant(&mut invariants, i, l.tokens)?;
        } else {
            return Err(Error::new_spanned(attr, "expected #[invariant(...)]"));
        }
    }
    // If there is only one invariant, remove its loop number
    if n_invariants == 1 {
        invariants.iter_mut().for_each(|i| {
            if let Tag::Invariant(LoopInvariant(ref mut kind)) = i.tag {
                *kind = None;
            }
        });
    }
    Ok(invariants)
}

fn while_to_loop(w: ExprWhile) -> ExprLoop {
    let sp = w.span();
    let body = w.body;
    let body = match *w.cond {
        Expr::Let(expr_let) => {
            quote_spanned! {sp=> #[allow(irrefutable_let_patterns)] if #expr_let #body else { break; } }
        }
        cond => quote_spanned! {sp=> if #cond #body else { break; } },
    };
    let body =
        Block { brace_token: Brace(sp), stmts: vec![Stmt::Expr(Expr::Verbatim(body), None)] };
    ExprLoop {
        attrs: w.attrs,
        label: w.label,
        loop_token: Token![loop](w.while_token.span),
        body: body,
    }
}

fn desugar_while(invariants: Vec<Invariant>, w: ExprWhile) -> TokenStream {
    desugar_loop(invariants, while_to_loop(w))
}

fn desugar_loop(invariants: Vec<Invariant>, mut l: ExprLoop) -> TokenStream {
    let span = l.loop_token.span;
    l.body.stmts.insert(0, Stmt::Expr(Expr::Verbatim(quote! { #(#invariants)* }), None));
    quote_spanned! {span=> {
      #[allow(unused_must_use)]
      let _ = { #[creusot::no_translate] #[creusot::before_loop] || {} };
      #l
    }}
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

    invariants.insert(0,
        Invariant {
            tag: Tag::Invariant(ForInvariant),
            span: for_span,
            term: parse_quote_spanned! {for_span=> ::creusot_contracts::std::iter::Iterator::produces(#iter_old.inner(), #produced.inner(), #it) },
        },
    );

    invariants.insert(
        0,
        Invariant {
            tag: Tag::Invariant(ForInvariant),
            span: for_span,
            term: parse_quote_spanned! {for_span=> ::creusot_contracts::invariant::inv(#it) },
        },
    );

    invariants.insert(0,
        Invariant {
            tag: Tag::Invariant(ForInvariant),
            span: for_span,
            term: parse_quote_spanned! {for_span=> ::creusot_contracts::invariant::inv(*#produced) },
        },
    );

    let elem = Ident::new("__creusot_proc_iter_elem", proc_macro::Span::def_site().into());

    // Note: the type of `produced` is not determined from its definition alone.
    // We expect:
    // ```
    //     let produced: Snapshot<Seq<&T::Item>> = ...
    // ```
    // where `T: Iterator` is the type of `it`.
    // This is indirectly enforced by typechecking the subsequent `produces` invariant.
    // This may thus break if we change the order of invariants.
    quote_spanned! {for_span=> {
        let mut #it = ::std::iter::IntoIterator::into_iter(#iter);
        let #iter_old = snapshot! { #it };
        let mut #produced = snapshot! { ::creusot_contracts::logic::Seq::EMPTY };
        let _ = { #[creusot::before_loop] || {} };
        #(#outer)*
        #lbl
        loop {
            #(#inner)*
            #(#invariants)*
            match ::std::iter::Iterator::next(&mut #it) {
                Some(#elem) => {
                    #[allow(unused_assignments)]
                    #produced = snapshot! { #produced.inner().concat(::creusot_contracts::logic::Seq::singleton(#elem)) };
                    let #pat = #elem;
                    #body
                },
                None => break,
            }
        }
    } }
}

pub(crate) fn desugar_variant(attr: TokenStream, tokens: TokenStream) -> Result<TokenStream> {
    match syn::parse2(tokens.clone()) {
        Ok(f) => desugar_variant_fn(attr, f),
        _ => desugar(Tag::Variant, attr, tokens),
    }
}

fn variant_to_tokens(span: Span, p: &pearlite_syn::Term) -> (String, TokenStream) {
    let var_name = crate::generate_unique_ident("variant");
    let var_body = pretyping::encode_term(p).unwrap_or_else(|e| {
        return e.into_tokens();
    });
    let name_tag = format!("{}", var_name);

    let variant_tokens = quote_spanned! {span=>
        #[allow(unused_must_use)]
        let _ =
            #[creusot::no_translate]
            #[creusot::item=#name_tag]
            #[creusot::spec::variant]
            #[creusot::spec]
            ||{ ::creusot_contracts::__stubs::variant_check(#var_body) }
        ;
    };
    (name_tag, variant_tokens)
}

fn desugar_variant_fn(attr: TokenStream, mut f: ItemFn) -> Result<TokenStream> {
    let span = attr.span();
    let p = syn::parse2(attr)?;
    let (name_tag, variant_tokens) = variant_to_tokens(span, &p);

    f.block.stmts.insert(0, Stmt::Item(syn::Item::Verbatim(variant_tokens)));
    Ok(quote! {
        #[creusot::clause::variant=#name_tag]
        #f
    })
}
