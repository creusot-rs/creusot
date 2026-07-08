//! Attributes that can be put on program functions to specify their contract.

use crate::{
    common::ContractSubject,
    creusot::{
        doc::{self, document_spec},
        pretyping,
    },
};
use pearlite_syn::{EnsuresTerm, Term, TermPath};
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    Attribute, Block, Expr, Ident, Item, Pat, Path, ReturnType, Stmt, Token, Type, parenthesized,
    parse::{self, Parse},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    spanned::Spanned as _,
    token::{self, Comma},
};

pub fn requires(attr: TS1, tokens: TS1) -> TS1 {
    const REQUIRES_LEN: usize = "#[requires(".len();
    let documentation = document_spec("requires", doc::LogicBody::term(REQUIRES_LEN, attr.clone()));

    let mut item = parse_macro_input!(tokens as ContractSubject);
    let req_body = pretyping::encode_term(&parse_macro_input!(attr as Term));
    item.mark_unused();

    let req_name = crate::creusot::generate_unique_ident(&item.name(), Span::call_site());
    let name_tag = req_name.to_string();
    let requires_tokens = fn_spec_item(req_name.clone(), FnSpecResultKind::NoResult, req_body);
    use ContractSubject::*;
    match item {
        FnOrMethod(mut fn_or_meth) => {
            let ty_result = match fn_or_meth.sig.output {
                ReturnType::Default => parse_quote! { () },
                ReturnType::Type(_, ref ty) => (**ty).clone(),
            };
            let attrs = std::mem::take(&mut fn_or_meth.attrs);

            let mut companion = TokenStream::new();
            if let Some(b) = fn_or_meth.body.as_mut() {
                b.stmts.insert(0, Stmt::Item(Item::Verbatim(requires_tokens)));
            } else {
                assert!(fn_or_meth.is_trait_signature());
                let mut sig = fn_or_meth.sig.clone();
                sig.ident = req_name.clone();
                // Make sure the spec method has a prototype which is very similar to the original one,
                // To guarantee that they have the same ParamEnv
                // (in particular, they have the same early/late bound variables)
                sig.output = parse_quote! { -> ::core::marker::PhantomData<#ty_result> };

                companion = quote! {
                    #[creusot::no_translate]
                    #[doc(hidden)]
                    #sig {
                        #requires_tokens
                        ::core::marker::PhantomData
                    }
                };
            }

            TS1::from(quote! {
                #companion

                #[creusot::clause::requires=#name_tag]
                #(#attrs)*
                #documentation
                #fn_or_meth
            })
        }
        Const(item) => syn::Error::new(item.span(), "Unexpected `requires` on `const` item")
            .to_compile_error()
            .into(),
        Closure(mut clos) => {
            let body = &clos.body;
            *clos.body = parse_quote!({let res = #body; #requires_tokens res});
            TS1::from(quote! {
              #[creusot::clause::requires=#name_tag]
              #clos
            })
        }
    }
}

pub fn ensures(attr: TS1, tokens: TS1) -> TS1 {
    const ENSURES_LEN: usize = "#[ensures(".len();
    let documentation = document_spec("ensures", doc::LogicBody::term(ENSURES_LEN, attr.clone()));

    let mut item = parse_macro_input!(tokens as ContractSubject);
    let (result, ens_body) = match parse_macro_input!(attr as EnsuresTerm) {
        EnsuresTerm::EnsuresClosure(closure) => {
            if matches!(item, ContractSubject::Closure(_)) {
                return syn::Error::new(
                    closure.span(),
                    "The syntax #[ensures(|res| ...)] is not supported for specifying closures.",
                )
                .into_compile_error()
                .into();
            }
            (closure.result, pretyping::encode_term_with_triggers(&closure.body))
        }
        EnsuresTerm::TermWithTriggers(term) => {
            let result = ident_to_pat(Ident::new("result", Span::call_site()));
            (result, pretyping::encode_term_with_triggers(&term))
        }
    };
    item.mark_unused();

    let ens_name = crate::creusot::generate_unique_ident(&item.name(), Span::call_site());
    let name_tag = ens_name.clone().to_string();
    use ContractSubject::*;
    match item {
        FnOrMethod(mut fn_or_meth) => {
            let ty_result = match fn_or_meth.sig.output {
                ReturnType::Default => parse_quote! { () },
                ReturnType::Type(_, ref ty) => (**ty).clone(),
            };
            let ensures_tokens = fn_spec_item(
                ens_name.clone(),
                FnSpecResultKind::Typed(result, ty_result.clone()),
                ens_body,
            );
            let attrs = std::mem::take(&mut fn_or_meth.attrs);

            let mut companion = TokenStream::new();
            if let Some(b) = fn_or_meth.body.as_mut() {
                b.stmts.insert(0, Stmt::Item(Item::Verbatim(ensures_tokens)));
            } else {
                assert!(fn_or_meth.is_trait_signature());
                let mut sig = fn_or_meth.sig.clone();
                sig.ident = ens_name;
                // Make sure the spec method has a prototype which is very similar to the original one,
                // To guarantee that they have the same ParamEnv
                // (in particular, they have the same early/late bound variables)
                sig.output = parse_quote! { -> ::core::marker::PhantomData<#ty_result> };

                companion = quote! {
                    #[creusot::no_translate]
                    #[doc(hidden)]
                    #sig {
                        #ensures_tokens
                        ::core::marker::PhantomData
                    }
                };
            }

            TS1::from(quote! {
                #companion

                #[creusot::clause::ensures=#name_tag]
                #(#attrs)*
                #documentation
                #fn_or_meth
            })
        }
        Const(mut item) => {
            let ensures_tokens =
                fn_spec_item(ens_name.clone(), FnSpecResultKind::NoResult, ens_body);
            let attrs = std::mem::take(&mut item.attrs);
            let dummy = Expr::Tuple(syn::ExprTuple {
                attrs: vec![],
                paren_token: Default::default(),
                elems: Default::default(),
            });
            let expr = std::mem::replace(&mut *item.expr, dummy);
            let stmts = vec![Stmt::Item(Item::Verbatim(ensures_tokens)), Stmt::Expr(expr, None)];
            *item.expr = Expr::Block(syn::ExprBlock {
                attrs: vec![],
                label: None,
                block: Block { brace_token: Default::default(), stmts },
            });
            TS1::from(quote! {
                #[creusot::clause::ensures=#name_tag]
                #(#attrs)*
                #documentation
                #item
            })
        }
        Closure(mut clos) => {
            let res_id = Ident::new("res", Span::mixed_site());
            let ensures_tokens =
                fn_spec_item(ens_name, FnSpecResultKind::Unified(result, res_id.clone()), ens_body);

            let body = &clos.body;
            *clos.body = parse_quote!({
                let #res_id = #body;
                #ensures_tokens
                #res_id
            });
            TS1::from(quote! {
                #[creusot::clause::ensures=#name_tag]
                #clos
            })
        }
    }
}

pub fn maintains(attr: TS1, body: TS1) -> TS1 {
    let tokens = maintains_impl(attr, body);

    match tokens {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error().into(),
    }
}

pub fn check(args: TS1, tokens: TS1) -> TS1 {
    let mode = parse_macro_input!(args as Ident);
    let ghost = if mode == "terminates" {
        false
    } else if mode == "ghost" {
        true
    } else {
        let msg = format!("unknown mode `{mode}`. Accepted modes are `terminates` or `ghost`");
        return quote! { compile_error!(#msg) }.into();
    };
    let mut documentation = TokenStream::new();
    let mut clauses = TokenStream::new();
    if ghost {
        documentation.extend(document_spec("ghost", doc::LogicBody::None));
        clauses.extend(quote!(#[creusot::clause::check_ghost]));
    } else {
        documentation.extend(document_spec("terminates", doc::LogicBody::None));
        clauses.extend(quote!(#[creusot::clause::check_terminates]));
    }
    let item = tokens.clone();
    let item = parse_macro_input!(item as ContractSubject);
    if ghost
        && let ContractSubject::FnOrMethod(fn_or_method) = &item
        && let Some(def) = &fn_or_method.defaultness
    {
        return syn::Error::new(def.span(), "`ghost` functions cannot use the `default` modifier")
            .into_compile_error()
            .into();
    }

    let Attributes { attrs, rest } = syn::parse(tokens).unwrap();
    let mut result = quote! {
        #clauses
        #(#attrs)*
        #documentation
        #rest
    };
    if ghost && let ContractSubject::Closure(_) = item {
        // Implement `FnGhost` on the closure
        result = quote! {
            ::creusot_std::ghost::FnGhostWrapper::__new(#result)
        }
    }
    result.into()
}

pub fn bitwise_proof(_: TS1, tokens: TS1) -> TS1 {
    let tokens: TokenStream = tokens.into();
    TS1::from(quote! {
        #[creusot::bitwise]
        #tokens
    })
}

pub fn variant(attr: TS1, tokens: TS1) -> TS1 {
    super::invariant::desugar_variant(attr.into(), tokens.into())
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

/// A structure to parse some attributes followed by something else.
struct Attributes {
    attrs: Vec<Attribute>,
    rest: proc_macro2::TokenStream,
}
impl Parse for Attributes {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let attrs = Attribute::parse_outer(input).unwrap_or_else(|_| Vec::new());
        let rest = input.parse()?;
        Ok(Self { attrs, rest })
    }
}

enum FnSpecResultKind {
    NoResult,            // No result identifier (for ensures clauses)
    Typed(Pat, Type),    // The result identifier is typed explicitly (i.e. `|result : #ty| ...`)
    Unified(Pat, Ident), // The type of the result identifier is unified with the type of another variable
}

// Generate a token stream for the item representing a specific
// `requires` or `ensures`
fn fn_spec_item(tag: Ident, reskind: FnSpecResultKind, fn_spec_body: TokenStream) -> TokenStream {
    let name_tag = tag.to_string();
    let unify_ty_result = if let FnSpecResultKind::Unified(result, res) = &reskind {
        // Tell type inference that res and result have the same type
        quote! { ::creusot_std::__stubs::closure_result(#res, #result); }
    } else {
        quote! {}
    };

    let result_bind = match &reskind {
        FnSpecResultKind::NoResult => quote! {},
        FnSpecResultKind::Unified(result, _) => quote! { #result },
        FnSpecResultKind::Typed(result, ty) => quote! { #result: #ty },
    };

    quote! {
        #[allow(let_underscore_drop)]
        let _ =
            #[creusot::no_translate]
            #[creusot::item=#name_tag]
            #[creusot::spec]
            |#result_bind| -> bool { #unify_ty_result #fn_spec_body }
        ;
    }
}

type PearliteExpr = Term;

struct Maintains {
    receiver: Option<MaintainsArg>,
    invariant: Path,
    args: Punctuated<MaintainsArg, Comma>,
}

enum MaintainsArg {
    Mut(PearliteExpr),
    Immut(PearliteExpr),
}

impl Parse for MaintainsArg {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        if input.peek(Token![mut]) {
            let _: Token![mut] = input.parse()?;

            Ok(Self::Mut(input.parse()?))
        } else {
            Ok(Self::Immut(input.parse()?))
        }
    }
}

impl Parse for Maintains {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let receiver = if input.peek(token::Paren) {
            let content;
            let _ = parenthesized!(content in input);
            let _: Token![.] = input.parse()?;
            Some(content.parse()?)
        } else if input.peek2(Token![.]) {
            let arg: TermPath = input.parse()?;
            let _: Token![.] = input.parse()?;
            Some(MaintainsArg::Immut(Term::Path(arg)))
        } else {
            None
        };

        let property: Path = input.parse()?;

        let content;
        let _ = parenthesized!(content in input);
        let args = Punctuated::parse_terminated(&content)?;

        Ok(Maintains { receiver, invariant: property, args })
    }
}

fn maintains_tokens(mntn: &Maintains, pre: bool) -> TokenStream {
    let mut args = Vec::new();
    for a in &mntn.args {
        match a {
            MaintainsArg::Mut(a) => {
                if pre {
                    args.push(quote! { * (#a) })
                } else {
                    args.push(quote! { ^ (#a) })
                }
            }
            MaintainsArg::Immut(a) => args.push(quote! { #a }),
        }
    }

    let inv = &mntn.invariant;
    if mntn.receiver.is_some() {
        let recv = &mntn.receiver.as_ref().unwrap();
        let recv = match recv {
            MaintainsArg::Mut(a) if pre => quote! { * (#a) },
            MaintainsArg::Mut(a) => quote! { ^ (#a) },
            MaintainsArg::Immut(a) => quote! { #a },
        };
        quote! {
          (#recv) . #inv (#(#args),*)
        }
    } else {
        quote! {
          #inv (#(#args),*)
        }
    }
}

fn maintains_impl(attr: TS1, body: TS1) -> syn::Result<TS1> {
    let maintains: Maintains = syn::parse(attr)?;

    let pre_toks = maintains_tokens(&maintains, true);
    let post_toks = maintains_tokens(&maintains, false);
    let body = TokenStream::from(body);
    Ok(quote! {
      #[::creusot_std::macros::requires(#pre_toks)]
      #[::creusot_std::macros::ensures(#post_toks)]
      #body
    }
    .into())
}

fn ident_to_pat(i: Ident) -> Pat {
    Pat::Path(syn::ExprPath { attrs: vec![], qself: None, path: i.into() })
}
