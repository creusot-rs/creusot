#![feature(box_patterns, extract_if, extend_one, proc_macro_def_site, proc_macro_span)]

extern crate proc_macro;

use pearlite_syn::*;
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens, TokenStreamExt};
use std::iter;
use syn::{
    parse::{Parse, Result},
    spanned::Spanned,
    *,
};

mod derive;
mod doc;
mod extern_spec;
mod ghost;
mod invariant;
mod maintains;
mod pretyping;

use doc::document_spec;
use extern_spec::ExternSpecs;

trait FilterAttrs<'a> {
    type Ret: Iterator<Item = &'a Attribute>;

    fn outer(self) -> Self::Ret;
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
}

pub(crate) fn generate_unique_ident(prefix: &str) -> Ident {
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

        Ok(ContractSubject::FnOrMethod(FnOrMethod {
            defaultness,
            visibility: vis,
            attrs,
            sig,
            body: brace_token.map(|brace_token| Block { brace_token, stmts }),
            semi_token,
        }))
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

#[proc_macro_attribute]
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
                ReturnType::Default => parse_quote! { result : () },
                ReturnType::Type(_, ref ty) => parse_quote! { result : #ty },
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
                ReturnType::Default => parse_quote! { result : () },
                ReturnType::Type(_, ref ty) => parse_quote! { result : #ty },
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
                #[allow(unused_must_use)]
                let _ =
                    #attrs
                    |result| {::creusot_contracts::__stubs::closure_result(res, result); #req_body }
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

#[proc_macro_attribute]
pub fn variant(attr: TS1, tokens: TS1) -> TS1 {
    invariant::desugar_variant(attr.into(), tokens.into())
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

struct Assertion(Vec<TermStmt>);

impl Parse for Assertion {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let stmts = input.call(TBlock::parse_within)?;
        Ok(Assertion(stmts))
    }
}

#[proc_macro]
pub fn proof_assert(assertion: TS1) -> TS1 {
    let assert = parse_macro_input!(assertion as Assertion);
    let assert_body = pretyping::encode_block(&assert.0).unwrap_or_else(|e| e.into_tokens());

    TS1::from(quote! {
        {
            #[allow(unused_must_use)]
            let _ = {
                #[creusot::no_translate]
                #[creusot::spec]
                #[creusot::spec::assert]
                || -> bool { #assert_body }
            };
        }
    })
}

#[proc_macro]
pub fn snapshot(assertion: TS1) -> TS1 {
    let assert = parse_macro_input!(assertion as Assertion);
    let assert_body = pretyping::encode_block(&assert.0).unwrap_or_else(|e| e.into_tokens());

    TS1::from(quote! {
        {
            ::creusot_contracts::__stubs::snapshot_from_fn(
                #[creusot::no_translate]
                #[creusot::spec]
                #[creusot::spec::snapshot]
                || { ::creusot_contracts::snapshot::Snapshot::new (#assert_body) }
            )
        }
    })
}

/// A structure to parse some attributes followed by something else.
struct Attributes {
    attrs: Vec<Attribute>,
    rest: proc_macro2::TokenStream,
}
impl Parse for Attributes {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = Attribute::parse_outer(input).unwrap_or_else(|_| Vec::new());
        let rest = input.parse()?;
        Ok(Self { attrs, rest })
    }
}

#[proc_macro_attribute]
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

#[proc_macro_attribute]
pub fn pure(_: TS1, tokens: TS1) -> TS1 {
    let documentation = document_spec("pure", doc::LogicBody::None);
    if let Ok(item) = syn::parse::<ImplItemFn>(tokens.clone()) {
        if let Some(def) = item.defaultness {
            return syn::Error::new(
                def.span(),
                "`pure` functions cannot use the `default` modifier",
            )
            .into_compile_error()
            .into();
        }
    };
    let Attributes { attrs, rest } = syn::parse(tokens).unwrap();
    quote! {
        #[creusot::clause::no_panic]
        #[creusot::clause::terminates]
        #(#attrs)*
        #documentation
        #rest
    }
    .into()
}

#[proc_macro]
pub fn ghost(body: TS1) -> TS1 {
    let body = proc_macro2::TokenStream::from(ghost::ghost_preprocess(body));
    TS1::from(quote! {
        {
            ::creusot_contracts::__stubs::ghost_from_fn({
                #[creusot::ghost]
                #[::creusot_contracts::pure]
                || ::creusot_contracts::ghost::GhostBox::new({ #body })
            },
            ())
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
        let default: Option<_> = input.parse()?;
        if default.is_some() {
            return Err(syn::Error::new(
                input.span(),
                "logical functions cannot use the `default` modifier",
            ));
        }
        let sig: Signature = input.parse()?;
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![;]) {
            let semi_token: Token![;] = input.parse()?;
            Ok(LogicInput::Sig(TraitItemSignature { attrs, defaultness: default, sig, semi_token }))
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

impl LogicInput {
    fn logic_body(&self) -> doc::LogicBody {
        match self {
            LogicInput::Item(log_item) => {
                if doc::is_trusted(&log_item.attrs) {
                    doc::LogicBody::Trusted
                } else {
                    doc::LogicBody::Some(log_item.body.to_token_stream().into())
                }
            }
            LogicInput::Sig(_) => doc::LogicBody::None,
        }
    }
}

enum LogicKind {
    None,
    Prophetic,
    Law,
}

impl ToTokens for LogicKind {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::None | Self::Law => {}
            Self::Prophetic => tokens.extend(quote!(#[creusot::decl::logic::prophetic])),
        }
    }
}

#[proc_macro_attribute]
pub fn logic(kind: TS1, tokens: TS1) -> TS1 {
    let kind = if kind.is_empty() {
        LogicKind::None
    } else {
        let t = parse_macro_input!(kind as Ident);
        if t == "prophetic" {
            LogicKind::Prophetic
        } else if t == "law" {
            LogicKind::Law
        } else {
            return syn::Error::new(
                t.span(),
                "unsupported modifier. The only supported modifier at the moment is `prophetic`",
            )
            .into_compile_error()
            .into();
        }
    };
    let log = parse_macro_input!(tokens as LogicInput);
    let documentation = document_spec(
        match kind {
            LogicKind::None => "logic",
            LogicKind::Prophetic => "logic(prophetic)",
            LogicKind::Law => "law",
        },
        if matches!(kind, LogicKind::Law) { doc::LogicBody::None } else { log.logic_body() },
    );
    match log {
        LogicInput::Item(log) => logic_item(log, kind, documentation),
        LogicInput::Sig(sig) => logic_sig(sig, kind, documentation),
    }
}

fn logic_sig(mut sig: TraitItemSignature, kind: LogicKind, documentation: TokenStream) -> TS1 {
    let span = sig.span();
    let attrs = std::mem::take(&mut sig.attrs);

    TS1::from(quote_spanned! {span =>
        #[creusot::decl::logic]
        #kind
        #(#attrs)*
        #documentation
        #sig
    })
}

fn logic_item(log: LogicItem, kind: LogicKind, documentation: TokenStream) -> TS1 {
    let span = log.sig.span();

    let term = log.body;
    let vis = log.vis;
    let def = log.defaultness;
    let sig = log.sig;
    let attrs = log.attrs;
    let req_body = pretyping::encode_block(&term.stmts).unwrap_or_else(|e| e.into_tokens());

    TS1::from(quote_spanned! {span =>
        #[creusot::decl::logic]
        #kind
        #(#attrs)*
        #documentation
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
        #[creusot::decl::no_trigger]
        #[::creusot_contracts::logic(law)]
        #tokens
    })
}

#[proc_macro_attribute]
pub fn predicate(prophetic: TS1, tokens: TS1) -> TS1 {
    let prophetic = if prophetic.is_empty() {
        None
    } else {
        let t = parse_macro_input!(prophetic as Ident);
        if t == "prophetic" {
            Some(quote!(#[creusot::decl::logic::prophetic]))
        } else {
            None
        }
    };

    let pred = parse_macro_input!(tokens as LogicInput);

    let sig = match &pred {
        LogicInput::Item(LogicItem { sig, .. }) => sig,
        LogicInput::Sig(TraitItemSignature { sig, .. }) => sig,
    };

    let is_bool = match &sig.output {
        ReturnType::Default => false,
        ReturnType::Type(_, ty) => *ty == parse_quote! { bool },
    };

    if !is_bool {
        let sp = match sig.output {
            ReturnType::Default => sig.span(),
            ReturnType::Type(_, _) => sig.output.span(),
        };
        return quote_spanned! {sp=> compile_error!("Predicates must have boolean return types"); }
            .into();
    };

    let documentation = document_spec(
        if prophetic.is_some() { "logic(prophetic)" } else { "logic" },
        pred.logic_body(),
    );

    match pred {
        LogicInput::Item(log) => predicate_item(log, prophetic, documentation),
        LogicInput::Sig(sig) => predicate_sig(sig, prophetic, documentation),
    }
}

fn predicate_sig(
    mut sig: TraitItemSignature,
    prophetic: Option<TokenStream>,
    documentation: TokenStream,
) -> TS1 {
    let span = sig.span();
    let attrs = std::mem::take(&mut sig.attrs);
    TS1::from(quote_spanned! {span =>
        #[creusot::decl::predicate]
        #prophetic
        #(#attrs)*
        #documentation
        #sig
    })
}

fn predicate_item(
    log: LogicItem,
    prophetic: Option<TokenStream>,
    documentation: TokenStream,
) -> TS1 {
    let span = log.sig.span();
    let term = log.body;
    let vis = log.vis;
    let def = log.defaultness;
    let sig = log.sig;
    let attrs = log.attrs;

    let req_body = pretyping::encode_block(&term.stmts).unwrap_or_else(|e| e.into_tokens());

    TS1::from(quote_spanned! {span =>
        #[creusot::decl::predicate]
        #prophetic
        #(#attrs)*
        #documentation
        #vis #def #sig {
            #req_body
        }
    })
}

#[proc_macro_attribute]
pub fn open_inv_result(_: TS1, tokens: TS1) -> TS1 {
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::open_inv_result]
        #tokens
    })
}

#[proc_macro_attribute]
pub fn trusted(_: TS1, tokens: TS1) -> TS1 {
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
            .unwrap_or_else(|e| e.into_tokens()),
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

    TS1::from(quote! {
        #(#[creusot::extern_spec]
          #specs
        )*
    })
}

#[proc_macro_attribute]
pub fn maintains(attr: TS1, body: TS1) -> TS1 {
    let tokens = maintains::maintains_impl(attr, body);

    match tokens {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error().into(),
    }
}

#[proc_macro_attribute]
pub fn invariant(invariant: TS1, tokens: TS1) -> TS1 {
    invariant::desugar_invariant(invariant.into(), tokens.into())
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

#[proc_macro_attribute]
pub fn open(attr: TS1, body: TS1) -> TS1 {
    let item = parse_macro_input!(body as ContractSubject);

    let open_name = generate_unique_ident(&item.name());
    let name_tag = format!("{}", quote! { #open_name });
    let vis = if attr.is_empty() {
        Visibility::Public(Default::default())
    } else {
        Visibility::Restricted(VisRestricted {
            pub_token: Default::default(),
            paren_token: Default::default(),
            in_token: Default::default(),
            path: parse_macro_input!(attr),
        })
    };

    let open_tokens = quote! {
        #[creusot::no_translate]
        #[creusot::item=#name_tag]
        #vis fn #open_name() {}
    };

    match item {
        ContractSubject::FnOrMethod(fn_or_meth) if fn_or_meth.is_trait_signature() => TS1::from(
            Error::new(Span::call_site(), "Cannot mark trait item signature as open")
                .to_compile_error(),
        ),
        ContractSubject::FnOrMethod(mut f) => {
            if let Some(b) = f.body.as_mut() {
                b.stmts.insert(0, Stmt::Item(Item::Verbatim(open_tokens)))
            }
            TS1::from(quote! {
              #[creusot::clause::open=#name_tag]
              #f
            })
        }
        ContractSubject::Closure(_) => TS1::from(
            Error::new(Span::call_site(), "Cannot mark closure as open").to_compile_error(),
        ),
    }
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

#[proc_macro_derive(DeepModel, attributes(DeepModelTy))]
pub fn derive_deep_model(tokens: TS1) -> TS1 {
    derive::derive_deep_model(tokens)
}

#[proc_macro_derive(Resolve)]
pub fn derive_resolve(tokens: TS1) -> TS1 {
    derive::derive_resolve(tokens)
}
