use crate::creusot::pretyping;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    AttrStyle, Attribute, Block, Error, Expr, ExprForLoop, ExprLoop, ExprWhile, Ident, ItemFn,
    Meta, Result, Stmt, Token, parse_quote_spanned, spanned::Spanned, token::Brace,
};

#[derive(Debug, Clone, Copy)]
enum InvariantKind {
    ForInvariant,
    LoopInvariant(Option<usize>),
}
use InvariantKind::*;

#[derive(Debug, Clone, Copy)]
enum Tag {
    Invariant(InvariantKind),
    Variant,
}

/// Represents a loop invariant
#[derive(Debug)]
struct Invariant {
    /// Used to generate the label of the invariant
    kind: InvariantKind,
    /// Span of the attribute
    span: Span,
    term: pearlite_syn::Term,
}

/// Represents a loop variant
#[derive(Debug)]
struct Variant {
    /// Span of the attribute
    span: Span,
    term: pearlite_syn::Term,
}

impl ToTokens for Invariant {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.span;
        let term = pretyping::encode_term(&self.term);
        let spec_closure = {
            let expl = match self.kind {
                LoopInvariant(Some(n)) => format!("expl:loop invariant #{}", n),
                LoopInvariant(None) => "expl:loop invariant".to_string(),
                ForInvariant => "expl:for invariant".to_string(),
            };
            quote_spanned! {span=>
              #[creusot::spec::invariant = #expl]
              || { #term }
            }
        };
        tokens.extend(quote_spanned! {span=>
            #[allow(let_underscore_drop)]
            let _ =
                #[creusot::no_translate]
                #[creusot::spec]
                #spec_closure;
        })
    }
}

impl ToTokens for Variant {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.span;
        let term = pretyping::encode_term(&self.term);
        let spec_closure = quote_spanned! {span=>
          #[creusot::spec::variant::loop_]
          || { ::creusot_contracts::__stubs::variant_check(#term) }
        };
        tokens.extend(quote_spanned! {span=>
            #[allow(let_underscore_drop)]
            let _ =
                #[creusot::no_translate]
                #[creusot::spec]
                #spec_closure;
        })
    }
}

/// Desugars a loop invariant
pub fn desugar_invariant(invariant0: TokenStream, expr: TokenStream) -> Result<TokenStream> {
    desugar(Tag::Invariant(LoopInvariant(Some(0))), invariant0, expr)
}

/// Desugars a loop (in)variant
fn desugar(tag: Tag, invariant0: TokenStream, expr: TokenStream) -> Result<TokenStream> {
    let expr: Expr = syn::parse2(expr)?;
    let invariants = |attrs| filter_invariants(tag, invariant0, attrs);
    match expr {
        Expr::ForLoop(mut expr) => Ok(desugar_for(invariants(&mut expr.attrs)?, expr)),
        Expr::While(mut expr) => Ok(desugar_while(invariants(&mut expr.attrs)?, expr)),
        Expr::Loop(mut expr) => Ok(desugar_loop(invariants(&mut expr.attrs)?, expr)),
        _ => Err(Error::new_spanned(
            expr,
            format!(
                "{} must be attached to either a `for`, `loop` or `while`",
                match tag {
                    Tag::Invariant(_) => "invariant",
                    Tag::Variant => "variant",
                }
            ),
        )),
    }
}

/// Extract all the variant/invariants in `attrs`.
///
/// # Returns
///
/// Returns the list of invariants in `attrs`, prefixed by `invariant`.
/// Each invariant is given a number, corresponding to the order of appearance.
/// This number will be visible in why3's IDE.
fn filter_invariants(
    tag: Tag,
    invariant: TokenStream,
    attrs: &mut Vec<Attribute>,
) -> Result<(Vec<Invariant>, Option<Variant>)> {
    let mut n_invariants = if let Tag::Variant = &tag { 0 } else { 1 };
    let mut invariants = Vec::new();
    let mut variant = None;

    match tag {
        Tag::Invariant(kind) => invariants.push(Invariant {
            kind,
            span: invariant.span(),
            term: syn::parse2(invariant)?,
        }),
        Tag::Variant => {
            variant = Some(Variant { span: invariant.span(), term: syn::parse2(invariant)? })
        }
    }

    let attrs = attrs.extract_if(0.., |attr| {
        attr.path().get_ident().is_some_and(|i| i == "invariant" || i == "variant")
    });
    for attr in attrs {
        if attr.path().get_ident().map(|i| i == "invariant").unwrap_or(false) {
            n_invariants += 1;
            let kind = LoopInvariant(Some(n_invariants - 1));
            if let Meta::List(l) = attr.meta {
                invariants.push(Invariant {
                    kind,
                    span: l.tokens.span(),
                    term: syn::parse2(l.tokens)?,
                });
            } else {
                return Err(Error::new_spanned(attr, "expected #[invariant(...)]"));
            }
        } else {
            let attr_span = attr.span();
            if let Meta::List(l) = attr.meta {
                if variant.is_some() {
                    return Err(Error::new(attr_span, "Only one variant can be defined on a loop"));
                }
                variant = Some(Variant { span: l.tokens.span(), term: syn::parse2(l.tokens)? });
            } else {
                return Err(Error::new_spanned(attr, "expected #[variant(...)]"));
            }
        };
    }
    // If there is only one invariant, remove its loop number
    if n_invariants == 1 {
        for i in &mut invariants {
            i.kind = LoopInvariant(None);
        }
    }
    Ok((invariants, variant))
}

/// Desugar a `while` loop into a `loop`, by hand.
///
/// This is easier to insert invariants like this.
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
    ExprLoop { attrs: w.attrs, label: w.label, loop_token: Token![loop](w.while_token.span), body }
}

fn desugar_while(
    (invariants, variant): (Vec<Invariant>, Option<Variant>),
    w: ExprWhile,
) -> TokenStream {
    desugar_loop((invariants, variant), while_to_loop(w))
}

fn desugar_loop(
    (invariants, variant): (Vec<Invariant>, Option<Variant>),
    mut l: ExprLoop,
) -> TokenStream {
    let span = l.span();
    let variant = if let Some(variant) = variant { quote!(#variant) } else { TokenStream::new() };

    l.body.stmts.insert(0, Stmt::Expr(Expr::Verbatim(quote! { #variant #(#invariants)* }), None));
    quote_spanned! {span=> {
        #[allow(let_underscore_drop)]
        let _ = #[creusot::no_translate] #[creusot::before_loop] || {};
        #l
    }}
}

/// Lowers for loops to `loop` and inserts the structural invariant that we get 'for free'
fn desugar_for(
    (mut invariants, variant): (Vec<Invariant>, Option<Variant>),
    f: ExprForLoop,
) -> TokenStream {
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
            kind: ForInvariant,
            span: for_span,
            term: parse_quote_spanned! {for_span=> ::creusot_contracts::std::iter::IteratorSpec::produces(#iter_old.inner(), #produced.inner(), #it) },
        },
    );

    invariants.insert(0, Invariant {
        kind: ForInvariant,
        span: for_span,
        term: parse_quote_spanned! {for_span=> ::creusot_contracts::invariant::inv(*#produced) },
    });

    let elem = Ident::new("__creusot_proc_iter_elem", proc_macro::Span::def_site().into());

    let variant = if let Some(variant) = variant { quote!(#variant) } else { TokenStream::new() };

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
        let mut #produced = snapshot! { ::creusot_contracts::logic::Seq::empty() };
        let _ = { #[creusot::before_loop] || {} };
        #(#outer)*
        #lbl
        loop {
            #(#inner)*
            #variant
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

/// Desugar a variant. This can be attached to either a function or a loop.
pub(crate) fn desugar_variant(attr: TokenStream, tokens: TokenStream) -> Result<TokenStream> {
    match syn::parse2(tokens.clone()) {
        Ok(f) => desugar_variant_fn(attr, f),
        _ => desugar(Tag::Variant, attr, tokens),
    }
}

/// Generate the specification item corresponding to a function variant
fn variant_to_tokens(span: Span, p: &pearlite_syn::Term) -> (String, TokenStream) {
    let var_body = pretyping::encode_term(p);
    let name_tag = crate::creusot::generate_unique_string("variant");

    let variant_tokens = quote_spanned! {span=>
        #[allow(let_underscore_drop)]
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

/// Desugars a function variant
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
