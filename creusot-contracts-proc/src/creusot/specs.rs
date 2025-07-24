//! Attributes that can be put on program functions to specify their contract.

use super::{
    doc::{self, document_spec},
    generate_unique_ident, pretyping,
};
use crate::common::ContractSubject;
use pearlite_syn::{Term, TermPath};
use proc_macro::TokenStream as TS1;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    Attribute, FnArg, Ident, ImplItemFn, Item, Path, ReturnType, Signature, Stmt, Token,
    parenthesized,
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

    let req_name = generate_unique_ident(&item.name());

    let name_tag = format!("{}", quote! { #req_name });

    match item {
        ContractSubject::FnOrMethod(mut fn_or_meth) if fn_or_meth.is_trait_signature() => {
            let attrs = std::mem::take(&mut fn_or_meth.attrs);
            let requires_tokens = sig_spec_item(req_name, fn_or_meth.sig.clone(), term);
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
            let requires_tokens = fn_spec_item(req_name, None, term);

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
            let requires_tokens = fn_spec_item(req_name, None, term);
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

    let ens_name = generate_unique_ident(&item.name());
    let name_tag = format!("{}", quote! { #ens_name });

    match item {
        ContractSubject::FnOrMethod(mut s) if s.is_trait_signature() => {
            let attrs = std::mem::take(&mut s.attrs);
            let result = match s.sig.output {
                ReturnType::Default => parse_quote! { result: () },
                ReturnType::Type(_, ref ty) => parse_quote! { result: #ty },
            };

            let mut sig = s.sig.clone();
            sig.inputs.push(result);
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
            let result = match f.sig.output {
                ReturnType::Default => parse_quote! { result: () },
                ReturnType::Type(_, ref ty) => parse_quote! { result: #ty },
            };
            let ensures_tokens = fn_spec_item(ens_name, Some(result), term);

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
            let req_body = req_body(&term);
            let attrs = spec_attrs(&ens_name);
            let body = &clos.body;
            *clos.body = parse_quote!({
                let res = #body;
                #[allow(let_underscore_drop)]
                let _ =
                    #attrs
                    |result| -> bool {::creusot_contracts::__stubs::closure_result(res, result); #req_body }
                ;
                res
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

pub fn terminates(_: TS1, tokens: TS1) -> TS1 {
    let documentation = document_spec("terminates", doc::LogicBody::None);
    if let Ok(item) = syn::parse::<ImplItemFn>(tokens.clone()) {
        if let Some(def) = item.defaultness {
            return syn::Error::new(
                def.span(),
                "`terminates` functions cannot use the `default` modifier",
            )
            .into_compile_error()
            .into();
        }
    };

    let Attributes { attrs, rest } = syn::parse(tokens).unwrap();
    quote! {
        #[creusot::clause::terminates]
        #(#attrs)*
        #documentation
        #rest
    }
    .into()
}

pub fn pure(_: TS1, tokens: TS1) -> TS1 {
    let documentation = document_spec("pure", doc::LogicBody::None);
    let item = tokens.clone();
    let item = parse_macro_input!(item as ContractSubject);
    let is_closure = match item {
        ContractSubject::FnOrMethod(fn_or_method) => {
            if let Some(def) = fn_or_method.defaultness {
                return syn::Error::new(
                    def.span(),
                    "`pure` functions cannot use the `default` modifier",
                )
                .into_compile_error()
                .into();
            } else {
                false
            }
        }
        ContractSubject::Closure(_) => true,
    };
    let Attributes { attrs, rest } = syn::parse(tokens).unwrap();
    let mut result = quote! {
        #[creusot::clause::no_panic]
        #[creusot::clause::terminates]
        #(#attrs)*
        #documentation
        #rest
    };
    if is_closure {
        // Implement `FnPure` on the closure
        result = quote! {
            ::creusot_contracts::fn_pure::FnPureWrapper::__new(#result)
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

fn req_body(p: &Term) -> TokenStream {
    pretyping::encode_term(p).unwrap_or_else(|e| e.into_tokens())
}

fn spec_attrs(tag: &Ident) -> TokenStream {
    let name_tag = format!("{}", quote! { #tag });
    quote! {
         #[creusot::no_translate]
         #[creusot::item=#name_tag]
         #[creusot::spec]
         #[doc(hidden)]
    }
}

// Generate a token stream for the item representing a specific
// `requires` or `ensures`
fn fn_spec_item(tag: Ident, result: Option<FnArg>, p: Term) -> TokenStream {
    let req_body = req_body(&p);
    let attrs = spec_attrs(&tag);

    quote! {
        #[allow(let_underscore_drop)]
        let _ =
            #attrs
            |#result| -> bool { #req_body }
        ;
    }
}

fn sig_spec_item(tag: Ident, mut sig: Signature, p: Term) -> TokenStream {
    let req_body = req_body(&p);
    let attrs = spec_attrs(&tag);
    sig.ident = tag;
    sig.output = parse_quote! { -> bool };

    quote! {
        #attrs
        #sig { #req_body }
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
