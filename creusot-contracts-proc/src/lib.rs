#![feature(box_patterns, drain_filter, proc_macro_def_site)]
extern crate proc_macro;
use extern_spec::ExternSpecs;
use pearlite_syn::*;
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens, TokenStreamExt};
use std::iter;
use syn::{
    parse::{Parse, Result},
    spanned::Spanned,
    token::Brace,
    *,
};

mod extern_spec;
mod invariant;
mod maintains;
mod pretyping;

mod derive;

trait FilterAttrs<'a> {
    type Ret: Iterator<Item = &'a Attribute>;

    fn outer(self) -> Self::Ret;
    fn inner(self) -> Self::Ret;
}

impl<'a> FilterAttrs<'a> for &'a [Attribute] {
    type Ret = iter::Filter<std::slice::Iter<'a, Attribute>, fn(&&Attribute) -> bool>;

    fn outer(self) -> Self::Ret {
        fn is_outer(attr: &&Attribute) -> bool {
            match attr.style {
                AttrStyle::Outer => true,
                AttrStyle::Inner(_) => false,
            }
        }
        self.iter().filter(is_outer)
    }

    fn inner(self) -> Self::Ret {
        fn is_inner(attr: &&Attribute) -> bool {
            match attr.style {
                AttrStyle::Inner(_) => true,
                AttrStyle::Outer => false,
            }
        }
        self.iter().filter(is_inner)
    }
}

fn generate_unique_ident(prefix: &str) -> Ident {
    let uuid = uuid::Uuid::new_v4();
    let ident = format!("{}_{}", prefix, uuid).replace('-', "_");

    Ident::new(&ident, Span::call_site())
}

struct TraitItemSignature {
    attrs: Vec<Attribute>,
    defaultness: Option<Token![default]>,
    sig: Signature,
    semi_token: Token![;],
}

impl ToTokens for TraitItemSignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(self.attrs.outer());
        self.defaultness.to_tokens(tokens);
        self.sig.to_tokens(tokens);
        self.semi_token.to_tokens(tokens);
    }
}

struct FnOrMethod {
    defaultness: Option<Token![default]>,
    visibility: Visibility,
    attrs: Vec<Attribute>,
    sig: Signature,
    body: Option<Block>,
    semi_token: Option<Token![;]>,
}

impl FnOrMethod {
    fn is_trait_signature(&self) -> bool {
        self.semi_token.is_some()
    }
}

enum ContractSubject {
    FnOrMethod(FnOrMethod),
    Closure(ExprClosure),
}

impl ToTokens for FnOrMethod {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(self.attrs.outer());
        self.defaultness.to_tokens(tokens);
        self.visibility.to_tokens(tokens);
        self.sig.to_tokens(tokens);
        self.body.to_tokens(tokens);
        self.semi_token.to_tokens(tokens);
    }
}

impl ContractSubject {
    fn name(&self) -> String {
        match self {
            ContractSubject::FnOrMethod(tr) => tr.sig.ident.to_string(),
            ContractSubject::Closure(_) => "closure".to_string(),
        }
    }

    fn mark_unused(&mut self) {
        if let ContractSubject::FnOrMethod(sig) = self {
            for arg in sig.sig.inputs.iter_mut() {
                let attrs = match arg {
                    FnArg::Receiver(r) => &mut r.attrs,
                    FnArg::Typed(r) => &mut r.attrs,
                };
                attrs.push(parse_quote! { #[allow(unused)]});
            }
        }
    }
}

impl Parse for ContractSubject {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        if input.peek(Token![|])
            || input.peek(Token![async]) && (input.peek2(Token![|]) || input.peek2(Token![move]))
            || input.peek(Token![static])
            || input.peek(Token![move])
        {
            let mut closure: ExprClosure = input.parse()?;
            let _: Option<Token![,]> = input.parse()?;
            closure.attrs.extend(attrs);
            return Ok(ContractSubject::Closure(closure));
        }

        let defaultness: Option<_> = input.parse()?;
        // Infalliable, no visibility = inherited
        let vis: Visibility = input.parse()?;
        let sig: Signature = input.parse()?;
        let lookahead = input.lookahead1();

        let (brace_token, stmts, semi_token) = if lookahead.peek(token::Brace) {
            let content;
            let brace_token = braced!(content in input);

            let stmts = content.call(Block::parse_within)?;
            (Some(brace_token), stmts, None)
        } else if lookahead.peek(Token![;]) {
            let semi_token: Token![;] = input.parse()?;
            (None, Vec::new(), Some(semi_token))
        } else {
            return Err(lookahead.error());
        };

        return Ok(ContractSubject::FnOrMethod(FnOrMethod {
            defaultness,
            visibility: vis,
            attrs,
            sig,
            body: brace_token.map(|brace_token| Block { brace_token, stmts }),
            semi_token,
        }));
    }
}

fn req_body(p: &Term) -> TokenStream {
    pretyping::encode_term(p).unwrap_or_else(|e| {
        return e.into_tokens();
    })
}

fn spec_attrs(tag: &Ident) -> TokenStream {
    let name_tag = format!("{}", quote! { #tag });
    quote! {
         #[creusot::no_translate]
         #[creusot::item=#name_tag]
         #[creusot::decl::spec]
    }
}

// Generate a token stream for the item representing a specific
// `requires` or `ensures`
fn fn_spec_item(tag: Ident, result: Option<FnArg>, p: Term) -> TokenStream {
    let req_body = req_body(&p);
    let attrs = spec_attrs(&tag);

    quote! {
        #[allow(unused_must_use)]
        let _ =
            #attrs
            |#result|{ #req_body }
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

#[proc_macro_attribute]
pub fn requires(attr: TS1, tokens: TS1) -> TS1 {
    let mut item = parse_macro_input!(tokens as ContractSubject);
    let term = parse_macro_input!(attr as Term);
    item.mark_unused();

    let req_name = generate_unique_ident(&item.name());

    let name_tag = format!("{}", quote! { #req_name });

    match item {
        ContractSubject::FnOrMethod(fn_or_meth) if fn_or_meth.is_trait_signature() => {
            let requires_tokens = sig_spec_item(req_name, fn_or_meth.sig.clone(), term);
            TS1::from(quote! {
              #requires_tokens
              #[creusot::spec::requires=#name_tag]
              #fn_or_meth
            })
        }
        ContractSubject::FnOrMethod(mut f) => {
            let requires_tokens = fn_spec_item(req_name, None, term);

            f.body.as_mut().map(|b| b.stmts.insert(0, Stmt::Item(Item::Verbatim(requires_tokens))));
            TS1::from(quote! {
              #[creusot::spec::requires=#name_tag]
              #f
            })
        }
        ContractSubject::Closure(mut clos) => {
            let requires_tokens = fn_spec_item(req_name, None, term);
            let body = &clos.body;
            *clos.body = parse_quote!({let res = #body; #requires_tokens res});
            TS1::from(quote! {
              #[creusot::spec::requires=#name_tag]
              #clos
            })
        }
    }
}

#[proc_macro_attribute]
pub fn ensures(attr: TS1, tokens: TS1) -> TS1 {
    let mut item = parse_macro_input!(tokens as ContractSubject);
    let term = parse_macro_input!(attr as Term);
    item.mark_unused();

    let ens_name = generate_unique_ident(&item.name());
    let name_tag = format!("{}", quote! { #ens_name });

    match item {
        ContractSubject::FnOrMethod(s) if s.is_trait_signature() => {
            let result = match s.sig.output {
                ReturnType::Default => parse_quote! { result : () },
                ReturnType::Type(_, ref ty) => parse_quote! { result : #ty },
            };

            let mut sig = s.sig.clone();
            sig.inputs.push(result);
            let ensures_tokens = sig_spec_item(ens_name, sig, term);
            TS1::from(quote! {
              #ensures_tokens
              #[creusot::spec::ensures=#name_tag]
              #s
            })
        }
        ContractSubject::FnOrMethod(mut f) => {
            let result = match f.sig.output {
                ReturnType::Default => parse_quote! { result : () },
                ReturnType::Type(_, ref ty) => parse_quote! { result : #ty },
            };
            let ensures_tokens = fn_spec_item(ens_name, Some(result), term);

            f.body.as_mut().map(|b| b.stmts.insert(0, Stmt::Item(Item::Verbatim(ensures_tokens))));
            TS1::from(quote! {
                #[creusot::spec::ensures=#name_tag]
                #f
            })
        }
        ContractSubject::Closure(mut clos) => {
            let req_body = req_body(&term);
            let attrs = spec_attrs(&ens_name);
            let body = &clos.body;
            *clos.body = parse_quote!({
                let res = #body;
                #[allow(unused_must_use)]
                let _ =
                    #attrs
                    |result| {::creusot_contracts::__stubs::closure_result(res, result); #req_body }
                ;
                res});
            TS1::from(quote! {
              #[creusot::spec::ensures=#name_tag]
              #clos
            })
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

    let mut f: ItemFn = parse(tokens)?;

    let var_name = generate_unique_ident(&f.sig.ident.to_string());
    let mut var_sig = f.sig.clone();
    var_sig.ident = var_name.clone();
    // var_sig.output = parse_quote! { -> impl creusot_contracts::well_founded::WellFounded };
    let var_body = pretyping::encode_term(&p).unwrap_or_else(|e| {
        return e.into_tokens();
    });
    let name_tag = format!("{}", quote! { #var_name });

    let variant_tokens = quote! {
        #[allow(unused_must_use)]
        let _ =
            #[creusot::no_translate]
            #[creusot::item=#name_tag]
            #[creusot::decl::spec]
            ||{ ::creusot_contracts::__stubs::variant_check(#var_body) }
        ;
    };

    f.block.stmts.insert(0, Stmt::Item(Item::Verbatim(variant_tokens)));

    // TODO: Parse and pass down all the function's arguments.
    Ok(TS1::from(quote! {
      #[creusot::spec::variant=#name_tag]
      #f
    }))
}

struct Assertion(TBlock);

impl Parse for Assertion {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let stmts = input.call(TBlock::parse_within)?;
        Ok(Assertion(TBlock { brace_token: Brace { span: Span::call_site() }, stmts }))
    }
}

#[proc_macro]
pub fn proof_assert(assertion: TS1) -> TS1 {
    let assert = parse_macro_input!(assertion as Assertion);

    let assert_body = pretyping::encode_block(&assert.0).unwrap();

    TS1::from(quote! {
        {
            #[allow(unused_must_use)]
            let _ = {
                #[creusot::no_translate]
                #[creusot::decl::spec]
                #[creusot::spec::assert]
                || -> bool { #assert_body }
            };
        }
    })
}

#[proc_macro]
pub fn ghost(assertion: TS1) -> TS1 {
    let assertion = TokenStream::from(assertion);
    TS1::from(quote! {
        {
            (
                #[creusot::no_translate]
                #[creusot::decl::spec]
                #[creusot::spec::ghost]
                || { ::creusot_contracts::ghost::Ghost::new(#assertion) }
            )()
        }
    })
}

struct LogicItem {
    vis: Visibility,
    defaultness: Option<Token![default]>,
    attrs: Vec<Attribute>,
    sig: Signature,
    body: Box<TBlock>,
}

enum LogicInput {
    Item(LogicItem),
    Sig(TraitItemSignature),
}

impl Parse for LogicInput {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        // Infalliable, no visibility = inherited
        let vis: Visibility = input.parse()?;
        let default = input.parse()?;
        let sig: Signature = input.parse()?;
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![;]) {
            let semi_token: Token![;] = input.parse()?;
            return Ok(LogicInput::Sig(TraitItemSignature {
                attrs,
                defaultness: default,
                sig,
                semi_token,
            }));
        } else {
            let body;
            let brace_token = braced!(body in input);
            let stmts = body.call(TBlock::parse_within)?;

            Ok(LogicInput::Item(LogicItem {
                vis,
                defaultness: default,
                attrs,
                sig,
                body: Box::new(TBlock { brace_token, stmts }),
            }))
        }
    }
}

#[proc_macro_attribute]
pub fn logic(_: TS1, tokens: TS1) -> TS1 {
    let log = parse_macro_input!(tokens as LogicInput);
    match log {
        LogicInput::Item(log) => logic_item(log),
        LogicInput::Sig(sig) => logic_sig(sig),
    }
}

fn logic_sig(sig: TraitItemSignature) -> TS1 {
    let span = sig.span();
    TS1::from(quote_spanned! {span=>
        #[creusot::decl::logic]
        #sig
    })
}

fn logic_item(log: LogicItem) -> TS1 {
    let span = log.sig.span();

    let term = log.body;
    let vis = log.vis;
    let def = log.defaultness;
    let sig = log.sig;
    let attrs = log.attrs;
    let req_body = pretyping::encode_block(&term).unwrap();

    TS1::from(quote_spanned! {span=>
        #[creusot::decl::logic]
        #(#attrs)*
        #vis #def #sig {
            #req_body
        }
    })
}

#[proc_macro_attribute]
pub fn law(_: TS1, tokens: TS1) -> TS1 {
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::law]
        #[::creusot_contracts::logic]
        #tokens
    })
}

#[proc_macro_attribute]
pub fn predicate(_: TS1, tokens: TS1) -> TS1 {
    let pred = parse_macro_input!(tokens as LogicInput);

    match pred {
        LogicInput::Item(log) => predicate_item(log),
        LogicInput::Sig(sig) => predicate_sig(sig),
    }
}

fn predicate_sig(sig: TraitItemSignature) -> TS1 {
    let span = sig.span();
    TS1::from(quote_spanned! {span=>
        #[creusot::decl::predicate]
        #sig
    })
}

fn predicate_item(log: LogicItem) -> TS1 {
    let span = log.sig.span();
    let term = log.body;
    let vis = log.vis;
    let def = log.defaultness;
    let sig = log.sig;
    let attrs = log.attrs;

    let req_body = pretyping::encode_block(&term).unwrap();

    TS1::from(quote_spanned! {span=>
        #[creusot::decl::predicate]
        #(#attrs)*
        #vis #def #sig {
            #req_body
        }
    })
}

#[proc_macro_attribute]
pub fn trusted(_: TS1, tokens: TS1) -> TS1 {
    // let p: ItemFn = parse_macro_input!(tokens);
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::trusted]
        #[allow(creusot::experimental)]
        #tokens
    })
}

#[proc_macro]
pub fn pearlite(tokens: TS1) -> TS1 {
    let block = parse_macro_input!(tokens with TBlock::parse_within);
    TS1::from(
        block
            .iter()
            .map(pretyping::encode_stmt)
            .collect::<std::result::Result<TokenStream, _>>()
            .unwrap(),
    )
}

#[proc_macro]
pub fn extern_spec(tokens: TS1) -> TS1 {
    let externs: ExternSpecs = parse_macro_input!(tokens);

    let mut specs = Vec::new();
    let externs = match externs.flatten() {
        Ok(externs) => externs,
        Err(err) => return TS1::from(err.to_compile_error()),
    };

    for spec in externs {
        specs.push(spec.to_tokens());
    }

    return TS1::from(quote! {
        #(#[creusot::no_translate]
          #[creusot::extern_spec]
          #specs
        )*
    });
}

#[proc_macro_attribute]
pub fn maintains(attr: TS1, body: TS1) -> TS1 {
    let tokens = maintains::maintains_impl(attr, body);

    match tokens {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

#[proc_macro_attribute]
pub fn invariant(invariant: TS1, loopb: TS1) -> TS1 {
    let loop_ = match invariant::parse(invariant.into(), loopb.into()) {
        Ok(l) => l,
        Err(e) => return e.to_compile_error().into(),
    };

    invariant::lower(loop_).into()
}

// Derive Macros
#[proc_macro_derive(PartialEq)]
pub fn derive_partial_eq(tokens: TS1) -> TS1 {
    derive::derive_partial_eq(tokens)
}

#[proc_macro_derive(Clone)]
pub fn derive_clone(tokens: TS1) -> TS1 {
    derive::derive_clone(tokens)
}
