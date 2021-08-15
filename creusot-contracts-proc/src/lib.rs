extern crate proc_macro;

mod pretyping;

use proc_macro2::Span;
use syn::*;

use proc_macro::TokenStream as TS1;
use quote::quote;

fn generate_unique_ident(prefix: &str) -> Ident {
    let uuid = uuid::Uuid::new_v4();
    let ident = format!("{}_{}", prefix, uuid).replace('-', "_");

    Ident::new(&ident, Span::call_site())
}

#[proc_macro_attribute]
pub fn requires(attr: TS1, tokens: TS1) -> TS1 {
    let p: syn::Term = parse_macro_input!(attr);

    let f: ItemFn = parse_macro_input!(tokens);

    let req_name = generate_unique_ident(&f.sig.ident.to_string());
    let mut req_sig = f.sig.clone();
    req_sig.ident = req_name.clone();
    req_sig.output = parse_quote! { -> bool };
    let req_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #req_name });

    // TODO: Parse and pass down all the function's arguments.
    TS1::from(quote! {
      #[rustc_diagnostic_item=#name_tag]
      #[creusot::spec::no_translate]
      #req_sig {
        #req_body
      }

      #[creusot::spec::requires=#name_tag]
      #f
    })
}

#[proc_macro_attribute]
pub fn ensures(attr: TS1, tokens: TS1) -> TS1 {
    let p: syn::Term = parse_macro_input!(attr);

    let f: ItemFn = parse_macro_input!(tokens);

    let ens_name = generate_unique_ident(&f.sig.ident.to_string());
    let mut ens_sig = f.sig.clone();
    ens_sig.ident = ens_name.clone();
    let result = match ens_sig.output {
        ReturnType::Default => parse_quote! { result : () },
        ReturnType::Type(_, ty) => parse_quote! { result : #ty },
    };
    ens_sig.inputs.push(result);

    ens_sig.output = parse_quote! { -> bool };
    let ens_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #ens_name });

    TS1::from(quote! {
      #[rustc_diagnostic_item=#name_tag]
      #[creusot::spec::no_translate]
      #ens_sig {
        #ens_body
      }

      #[creusot::spec::ensures=#name_tag]
      #f
    })
}

#[proc_macro_attribute]
pub fn variant(attr: TS1, tokens: TS1) -> TS1 {
    let p: syn::Term = parse_macro_input!(attr);

    let f: ItemFn = parse_macro_input!(tokens);

    let var_name = generate_unique_ident(&f.sig.ident.to_string());
    let mut var_sig = f.sig.clone();
    var_sig.ident = var_name.clone();
    var_sig.output = parse_quote! { -> creusot_contracts::Int };
    let var_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #var_name });

    // TODO: Parse and pass down all the function's arguments.
    TS1::from(quote! {
      #[rustc_diagnostic_item=#name_tag]
      #[creusot::spec::no_translate]
      #var_sig {
        #var_body
      }

      #[creusot::spec::variant=#name_tag]
      #f
    })
}

struct Invariant {
    name: syn::Ident,
    invariant: syn::Term,
}

impl syn::parse::Parse for Invariant {
    fn parse(tokens: syn::parse::ParseStream) -> Result<Self> {
        let name = tokens.parse()?;
        let _: Token![,] = tokens.parse()?;
        let invariant = tokens.parse()?;

        Ok(Invariant { name, invariant })
    }
}
#[proc_macro_attribute]
pub fn invariant(invariant: TS1, loopb: TS1) -> TS1 {
    let inv: Invariant = parse_macro_input!(invariant);
    let term = inv.invariant;

    let inv_body = pretyping::encode_term(term).unwrap();

    let loopb = proc_macro2::TokenStream::from(loopb);
    let invariant_name = inv.name;
    let invariant_name = format!("{}", quote! { #invariant_name });

    TS1::from(quote! {
        {
            #[allow(unused_must_use)]
            let _ = {
                #[creusot::spec::no_translate]
                #[creusot::spec::invariant=#invariant_name]
                ||{ #inv_body }
            };
            #loopb
        }
    })
}

struct LogicItem {
    vis: Visibility,
    attrs: Vec<Attribute>,
    sig: Signature,
    body: Term,
}

impl syn::parse::Parse for LogicItem {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = Attribute::parse_outer(input)?;
        let vis = input.parse()?;
        let sig = input.parse()?;
        let body;
        braced!(body in input);
        let body = body.parse()?;

        Ok(LogicItem { vis, attrs, sig, body })
    }
}

#[proc_macro]
pub fn logic(body: TS1) -> TS1 {
    let log: LogicItem = parse_macro_input!(body);
    let term = log.body;
    let vis = log.vis;
    let sig = log.sig;
    let attrs = log.attrs;

    let req_body = pretyping::encode_term(term).unwrap();

    TS1::from(quote! {
        #[creusot::spec::logic]
        #(#attrs)*
        #vis #sig {
            #req_body
        }
    })
}

struct PredicateItem {
    vis: Visibility,
    attrs: Vec<Attribute>,
    sig: Signature,
    body: Term,
}

impl syn::parse::Parse for PredicateItem {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = Attribute::parse_outer(input)?;
        let vis = input.parse()?;
        let sig = input.parse()?;
        let body;
        braced!(body in input);
        let body = body.parse()?;

        Ok(PredicateItem { vis, attrs, sig, body })
    }
}

#[proc_macro]
pub fn predicate(tokens: TS1) -> TS1 {
    match syn::parse::<PredicateItem>(tokens.clone()) {
        Ok(log) => predicate_item(log),
        Err(_) => match syn::parse(tokens) {
            Ok(sig) => predicate_sig(sig),
            Err(err) => TS1::from(err.to_compile_error()),
        },
    }
}

fn predicate_sig(sig: TraitItemMethod) -> TS1 {
    TS1::from(quote! {
        #[creusot::spec::predicate]
        #sig
    })
}

fn predicate_item(log: PredicateItem) -> TS1 {
    let term = log.body;
    let term = format!("{}", quote! {#term});
    let vis = log.vis;
    let sig = log.sig;
    let attrs = log.attrs;
    TS1::from(quote! {
        #[creusot::spec::predicate=#term]
        #(#attrs)*
        #vis #sig {
            std::process::abort()
        }
    })
}
