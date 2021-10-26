extern crate proc_macro;

mod pretyping;

use pearlite_syn::*;
use proc_macro2::Span;
use syn::{parse::Result, *};

use proc_macro::TokenStream as TS1;
use proc_macro2::TokenStream;
use quote::quote;

fn generate_unique_ident(prefix: &str) -> Ident {
    let uuid = uuid::Uuid::new_v4();
    let ident = format!("{}_{}", prefix, uuid).replace('-', "_");

    Ident::new(&ident, Span::call_site())
}

// TODO: Add custom parse instance
enum FnOrTraitSig {
    Fn(ItemFn),
    TraitSig(TraitItemMethod),
}

impl FnOrTraitSig {
    pub fn sig(&self) -> Signature {
        match self {
            FnOrTraitSig::Fn(i) => i.sig.clone(),
            FnOrTraitSig::TraitSig(s) => s.sig.clone(),
        }
    }
}

fn parse_def_or_decl(tokens: TS1) -> Result<FnOrTraitSig> {
    syn::parse::<ItemFn>(tokens.clone())
        .map(FnOrTraitSig::Fn)
        .or_else(|_| syn::parse::<TraitItemMethod>(tokens.clone()).map(FnOrTraitSig::TraitSig))
}

// Generate a token stream for the item representing a specific
// `requires` or `ensures`
fn fn_spec_item(tag: Ident, result: Option<FnArg>, tokens: TS1) -> Result<TokenStream> {
    let p: pearlite_syn::Term = parse(tokens)?;
    let req_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #tag });

    Ok(quote! {
        #[allow(unused_must_use)]
        let _ =
            #[creusot::no_translate]
            #[creusot::item=#name_tag]
            #[creusot::decl::spec]
            |#result|{ #req_body }
        ;
    })
}

fn sig_spec_item(tag: Ident, mut sig: Signature, tokens: TS1) -> Result<TokenStream> {
    let p: pearlite_syn::Term = parse(tokens)?;
    let req_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #tag });
    sig.ident = tag;
    sig.output = parse_quote! { -> bool };

    Ok(quote! {
        #[creusot::no_translate]
        #[creusot::item=#name_tag]
        #[creusot::decl::spec]
        #sig { #req_body }
    })
}

#[proc_macro_attribute]
pub fn requires(attr: TS1, tokens: TS1) -> TS1 {
    match requires_inner(attr, tokens) {
        Ok(r) => r,
        Err(err) => return TS1::from(err.to_compile_error()),
    }
}

fn requires_inner(attr: TS1, tokens: TS1) -> Result<TS1> {
    let parse_res = parse_def_or_decl(tokens);

    let item = parse_res?;

    let req_name = generate_unique_ident(&item.sig().ident.to_string());

    let name_tag = format!("{}", quote! { #req_name });

    match item {
        FnOrTraitSig::Fn(mut f) => {
            let requires_tokens = fn_spec_item(req_name, None, attr)?;

            f.block.stmts.insert(0, Stmt::Item(Item::Verbatim(requires_tokens)));
            Ok(TS1::from(quote! {
              #[creusot::spec::requires=#name_tag]
              #f
            }))
        }
        FnOrTraitSig::TraitSig(s) => {
            let requires_tokens = sig_spec_item(req_name, s.sig.clone(), attr)?;
            Ok(TS1::from(quote! {

              #requires_tokens

              #[creusot::spec::requires=#name_tag]
              #s
            }))
        }
    }
}

#[proc_macro_attribute]
pub fn ensures(attr: TS1, tokens: TS1) -> TS1 {
    match ensures_inner(attr, tokens) {
        Ok(r) => r,
        Err(err) => return TS1::from(err.to_compile_error()),
    }
}

fn ensures_inner(attr: TS1, tokens: TS1) -> Result<TS1> {
    let item = parse_def_or_decl(tokens)?;

    let result = match item.sig().output {
        ReturnType::Default => parse_quote! { result : () },
        ReturnType::Type(_, ref ty) => parse_quote! { result : #ty },
    };

    let ens_name = generate_unique_ident(&item.sig().ident.to_string());
    let name_tag = format!("{}", quote! { #ens_name });

    match item {
        FnOrTraitSig::Fn(mut f) => {
            let ensures_tokens = fn_spec_item(ens_name, Some(result), attr)?;

            f.block.stmts.insert(0, Stmt::Item(Item::Verbatim(ensures_tokens)));
            Ok(TS1::from(quote! {
                #[creusot::spec::ensures=#name_tag]
                #f
            }))
        }
        FnOrTraitSig::TraitSig(s) => {
            let mut sig = s.sig.clone();
            sig.inputs.push(result);
            let ensures_tokens = sig_spec_item(ens_name, sig, attr)?;
            Ok(TS1::from(quote! {
              #ensures_tokens
              #[creusot::spec::ensures=#name_tag]
              #s
            }))
        }
    }
}

#[proc_macro_attribute]
pub fn variant(attr: TS1, tokens: TS1) -> TS1 {
    match variant_inner(attr, tokens) {
        Ok(r) => r,
        Err(err) => return TS1::from(err.to_compile_error()),
    }
}

fn variant_inner(attr: TS1, tokens: TS1) -> Result<TS1> {
    let p: pearlite_syn::Term = parse(attr)?;

    let f: ItemFn = parse(tokens)?;

    let var_name = generate_unique_ident(&f.sig.ident.to_string());
    let mut var_sig = f.sig.clone();
    var_sig.ident = var_name.clone();
    var_sig.output = parse_quote! { -> impl creusot_contracts::WellFounded };
    let var_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #var_name });

    // TODO: Parse and pass down all the function's arguments.
    Ok(TS1::from(quote! {
      #[creusot::item=#name_tag]
      #[creusot::no_translate]
      #[creusot::decl::spec]
      #var_sig {
        #var_body
      }

      #[creusot::spec::variant=#name_tag]
      #f
    }))
}

struct Invariant {
    name: syn::Ident,
    invariant: pearlite_syn::Term,
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
                #[creusot::no_translate]
                #[creusot::decl::spec]
                #[creusot::spec::invariant=#invariant_name]
                ||{ #inv_body }
            };
            #loopb
        }
    })
}

#[proc_macro]
pub fn proof_assert(assertion: TS1) -> TS1 {
    let assert: pearlite_syn::Term = parse_macro_input!(assertion);

    let assert_body = pretyping::encode_term(assert).unwrap();

    TS1::from(quote! {
        {
            #[allow(unused_must_use)]
            let _ = {
                #[creusot::no_translate]
                #[creusot::decl::spec]
                #[creusot::spec::assert]
                ||{ #assert_body }
            };
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

#[proc_macro_attribute]
pub fn logic(_: TS1, tokens: TS1) -> TS1 {
    match syn::parse::<LogicItem>(tokens.clone()) {
        Ok(log) => logic_item(log),
        Err(_) => match syn::parse(tokens) {
            Ok(sig) => logic_sig(sig),
            Err(err) => TS1::from(err.to_compile_error()),
        },
    }
}

fn logic_sig(sig: TraitItemMethod) -> TS1 {
    TS1::from(quote! {
        #[creusot::decl::logic]
        #sig
    })
}

fn logic_item(log: LogicItem) -> TS1 {
    let term = log.body;
    let vis = log.vis;
    let sig = log.sig;
    let attrs = log.attrs;

    let req_body = pretyping::encode_term(term).unwrap();

    TS1::from(quote! {
        #[creusot::decl::logic]
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

#[proc_macro_attribute]
pub fn predicate(_: TS1, tokens: TS1) -> TS1 {
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
        #[creusot::decl::predicate]
        #sig
    })
}

fn predicate_item(log: PredicateItem) -> TS1 {
    let term = log.body;
    let vis = log.vis;
    let sig = log.sig;
    let attrs = log.attrs;

    let req_body = pretyping::encode_term(term).unwrap();

    TS1::from(quote! {
        #[creusot::decl::predicate]
        #(#attrs)*
        #vis #sig {
            #req_body
        }
    })
}

#[proc_macro_attribute]
pub fn trusted(_: TS1, tokens: TS1) -> TS1 {
    let p: ItemFn = parse_macro_input!(tokens);

    TS1::from(quote! {
        #[creusot::decl::trusted]
        #p
    })
}

#[proc_macro]
pub fn pearlite(tokens: TS1) -> TS1 {
    let term: Term = parse_macro_input!(tokens);
    TS1::from(pretyping::encode_term(term).unwrap())
}
