//! Attributes that can be put on program functions to specify their contract.

use crate::{
    common::ContractSubject,
    creusot::{
        doc::{self, document_spec},
        pretyping,
    },
};
use pearlite_syn::{Term, TermPath};
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    Attribute, Ident, Item, Path, ReturnType, Signature, Stmt, Token, Type, parenthesized,
    parse::{self, Parse},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    spanned::Spanned as _,
    token::{self, Comma},
};

pub fn requires(attr: TS1, tokens: TS1) -> TS1 {
    let documentation = document_spec("requires", doc::LogicBody::Some(attr.clone()));

    let mut item = parse_macro_input!(tokens as ContractSubject);
    let term = parse_macro_input!(attr as Term);
    item.mark_unused();

    let req_name = crate::creusot::generate_unique_ident(&item.name(), Span::call_site());
    let name_tag = req_name.to_string();
    match item {
        ContractSubject::FnOrMethod(mut fn_or_meth) if fn_or_meth.is_trait_signature() => {
            let attrs = std::mem::take(&mut fn_or_meth.attrs);
            let mut sig = fn_or_meth.sig.clone();
            sig.ident = req_name.clone();
            sig.output = parse_quote! { -> bool };

            let requires_tokens = sig_spec_item(req_name, sig, term);
            TS1::from(quote! {
              #requires_tokens
              #[creusot::clause::requires=#name_tag]
              #(#attrs)*
              #documentation
              #fn_or_meth
            })
        }
        ContractSubject::FnOrMethod(mut f) => {
            let attrs = std::mem::take(&mut f.attrs);
            let requires_tokens = fn_spec_item(req_name, FnSpecResultKind::NoResult, term);

            if let Some(b) = f.body.as_mut() {
                b.stmts.insert(0, Stmt::Item(Item::Verbatim(requires_tokens)))
            }
            TS1::from(quote! {
              #[creusot::clause::requires=#name_tag]
              #(#attrs)*
              #documentation
              #f
            })
        }
        ContractSubject::Closure(mut clos) => {
            let requires_tokens = fn_spec_item(req_name, FnSpecResultKind::NoResult, term);
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
    let documentation = document_spec("ensures", doc::LogicBody::Some(attr.clone()));

    let mut item = parse_macro_input!(tokens as ContractSubject);
    let term = parse_macro_input!(attr as Term);
    item.mark_unused();

    let ens_name = crate::creusot::generate_unique_ident(&item.name(), Span::call_site());
    let name_tag = ens_name.to_string();
    match item {
        ContractSubject::FnOrMethod(mut s) if s.is_trait_signature() => {
            let attrs = std::mem::take(&mut s.attrs);
            let mut sig = s.sig.clone();
            let result = match sig.output {
                ReturnType::Default => parse_quote! { result: () },
                ReturnType::Type(_, ty) => parse_quote! { result: #ty },
            };

            sig.ident = ens_name.clone();
            sig.inputs.push(result);
            sig.output = parse_quote! { -> bool };
            let ensures_tokens = sig_spec_item(ens_name, sig, term);
            TS1::from(quote! {
              #ensures_tokens
              #[creusot::clause::ensures=#name_tag]
              #(#attrs)*
              #documentation
              #s
            })
        }
        ContractSubject::FnOrMethod(mut f) => {
            let attrs = std::mem::take(&mut f.attrs);
            let ty_result = match f.sig.output {
                ReturnType::Default => parse_quote! { () },
                ReturnType::Type(_, ref ty) => (**ty).clone(),
            };
            let ensures_tokens = fn_spec_item(ens_name, FnSpecResultKind::Typed(ty_result), term);
            if let Some(b) = f.body.as_mut() {
                b.stmts.insert(0, Stmt::Item(Item::Verbatim(ensures_tokens)))
            }
            TS1::from(quote! {
                #[creusot::clause::ensures=#name_tag]
                #(#attrs)*
                #documentation
                #f
            })
        }
        ContractSubject::Closure(mut clos) => {
            let res_id = Ident::new("res", Span::mixed_site());
            let ensures_tokens =
                fn_spec_item(ens_name, FnSpecResultKind::Unified(res_id.clone()), term);

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
    let modes = parse_macro_input!(args with Punctuated<Ident, Token![,]>::parse_terminated);
    let mut terminates = false;
    let mut ghost = false;
    for mode in modes {
        let err = |msg| syn::Error::new(mode.span(), msg).into_compile_error().into();
        if mode == "terminates" {
            if terminates {
                return err("modes can only be specified once".to_string());
            }
            terminates = true;
        } else if mode == "ghost" {
            if ghost {
                return err("modes can only be specified once".to_string());
            }
            ghost = true;
            terminates = true;
        } else {
            return err(format!(
                "unknown mode `{mode}`. Accepted modes are `terminates` or `ghost`"
            ));
        }
    }

    if !(terminates || ghost) {
        return syn::Error::new(Span::call_site(), "you must specify at least one mode")
            .into_compile_error()
            .into();
    }
    let mut documentation = TokenStream::new();
    let mut clauses = TokenStream::new();
    if terminates {
        documentation.extend(document_spec("terminates", doc::LogicBody::None));
        clauses.extend(quote!(#[creusot::clause::check_terminates]));
    }
    if ghost {
        documentation.extend(document_spec("ghost", doc::LogicBody::None));
        clauses.extend(quote!(#[creusot::clause::check_ghost]));
    }

    let item = tokens.clone();
    let item = parse_macro_input!(item as ContractSubject);
    let is_closure = if ghost {
        match item {
            ContractSubject::FnOrMethod(fn_or_method) => {
                if let Some(def) = fn_or_method.defaultness {
                    return syn::Error::new(
                        def.span(),
                        "`ghost` functions cannot use the `default` modifier",
                    )
                    .into_compile_error()
                    .into();
                } else {
                    false
                }
            }
            ContractSubject::Closure(_) => true,
        }
    } else {
        false
    };

    let Attributes { attrs, rest } = syn::parse(tokens).unwrap();
    let mut result = quote! {
        #clauses
        #(#attrs)*
        #documentation
        #rest
    };
    if is_closure {
        // Implement `FnGhost` on the closure
        result = quote! {
            ::creusot_contracts::ghost::FnGhostWrapper::__new(#result)
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

fn fn_spec_body(p: &Term) -> TokenStream {
    pretyping::encode_term(p).unwrap_or_else(|e| e.into_tokens())
}

fn spec_attrs(tag: Ident) -> TokenStream {
    let name_tag = tag.to_string();
    quote! {
         #[creusot::no_translate]
         #[creusot::item=#name_tag]
         #[creusot::spec]
         #[doc(hidden)]
    }
}

enum FnSpecResultKind {
    NoResult,       // No result identifier (for ensures clauses)
    Typed(Type),    // The result identifier is typed explicitely (i.e. |result : #ty| ... )
    Unified(Ident), // The type of the result identifier is unified with the type of another variable
}

// Generate a token stream for the item representing a specific
// `requires` or `ensures`
fn fn_spec_item(tag: Ident, reskind: FnSpecResultKind, p: Term) -> TokenStream {
    let fn_spec_body = fn_spec_body(&p);
    let attrs = spec_attrs(tag);
    let result = Ident::new("result", Span::call_site());

    let unify_ty_result = if let FnSpecResultKind::Unified(res) = &reskind {
        // Tell type inference that res and result have the same type
        quote! { ::creusot_contracts::__stubs::closure_result(#res, #result); }
    } else {
        quote! {}
    };

    let result_bind = match &reskind {
        FnSpecResultKind::NoResult => quote! {},
        FnSpecResultKind::Unified(_) => quote! { #result },
        FnSpecResultKind::Typed(ty) => quote! { #result: #ty },
    };

    quote! {
        #[allow(let_underscore_drop)]
        let _ =
            #attrs
            |#result_bind| -> bool { #unify_ty_result #fn_spec_body }
        ;
    }
}

fn sig_spec_item(tag: Ident, sig: Signature, p: Term) -> TokenStream {
    let fn_spec_body = fn_spec_body(&p);
    let attrs = spec_attrs(tag);

    quote! {
        #attrs
        #sig { #fn_spec_body }
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
      #[::creusot_contracts::requires(#pre_toks)]
      #[::creusot_contracts::ensures(#post_toks)]
      #body
    }
    .into())
}
