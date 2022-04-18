// Implementation of the `maintains` macro.

use pearlite_syn::*;
use proc_macro::TokenStream as TS1;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse::{Parse, Result},
    punctuated::Punctuated,
    token::Comma,
    *,
};

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
    fn parse(input: parse::ParseStream) -> Result<Self> {
        if input.peek(Token![mut]) {
            let _: Token![mut] = input.parse()?;

            return Ok(Self::Mut(input.parse()?));
        } else {
            return Ok(Self::Immut(input.parse()?));
        }
    }
}

impl Parse for Maintains {
    fn parse(input: parse::ParseStream) -> Result<Self> {
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

pub fn maintains_impl(attr: TS1, body: TS1) -> Result<TS1> {
    let maintains: Maintains = parse(attr)?;

    let pre_toks = maintains_tokens(&maintains, true);
    let post_toks = maintains_tokens(&maintains, false);
    let body = TokenStream::from(body);
    Ok(quote! {
      #[requires(#pre_toks)]
      #[ensures(#post_toks)]
      #body
    }
    .into())
}
