//! Macros for defining logical functions

use super::{
    doc::{self, document_spec},
    pretyping,
};
use crate::common::{ContractSubject, FilterAttrs as _};
use pearlite_syn::TBlock;
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, TokenStreamExt as _, quote, quote_spanned};
use syn::{
    Attribute, Error, Ident, Item, Result, Signature, Stmt, Token, VisRestricted, Visibility,
    braced,
    parse::{self, Parse},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned as _,
};

pub fn logic(tags: TS1, tokens: TS1) -> TS1 {
    let tags_idents = parse_macro_input!(tags with Punctuated<Ident, Token![,]>::parse_terminated);
    let mut tags = LogicTag::NONE;
    for tag in tags_idents {
        if tag == "prophetic" {
            tags.add(LogicTag::PROPHETIC);
        } else if tag == "sealed" {
            tags.add(LogicTag::SEALED);
        } else if tag == "law" {
            tags.add(LogicTag::LAW);
        } else {
            return syn::Error::new(
                tag.span(),
                "unsupported modifier. The only supported modifiers are `prophetic` and `sealed`",
            )
            .into_compile_error()
            .into();
        }
    }
    let log = parse_macro_input!(tokens as LogicInput);

    let mut doc_str = "logic".to_string();
    if !tags.is_empty() {
        doc_str.push('(');
        let mut comma = false;
        for tag in [LogicTag::LAW, LogicTag::PROPHETIC, LogicTag::SEALED] {
            if tags.has(tag) {
                if comma {
                    doc_str.push_str(", ");
                }
                comma = true;
                doc_str.push_str(tag.doc_str());
            }
        }
        doc_str.push(')')
    }

    let documentation = document_spec(
        &doc_str,
        if tags.has(LogicTag::LAW) { doc::LogicBody::None } else { log.logic_body() },
    );

    match log {
        LogicInput::Item(log) => logic_item(log, tags, documentation),
        LogicInput::Sig(sig) => logic_sig(sig, tags, documentation),
    }
}

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

pub fn open(attr: TS1, body: TS1) -> TS1 {
    let item = parse_macro_input!(body as ContractSubject);
    let open_name = crate::creusot::generate_unique_ident(&item.name(), Span::call_site());
    let name_tag = open_name.to_string();
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

pub struct TraitItemSignature {
    pub attrs: Vec<Attribute>,
    pub defaultness: Option<Token![default]>,
    pub sig: Signature,
    pub semi_token: Token![;],
}

impl ToTokens for TraitItemSignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(self.attrs.outer());
        self.defaultness.to_tokens(tokens);
        self.sig.to_tokens(tokens);
        self.semi_token.to_tokens(tokens);
    }
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LogicTag(u8);

impl LogicTag {
    const NONE: Self = Self(0);
    const LAW: Self = Self(1);
    const PROPHETIC: Self = Self(2);
    const SEALED: Self = Self(4);

    fn has(self, tag: Self) -> bool {
        self.0 & tag.0 > 0
    }
    fn is_empty(self) -> bool {
        self.0 == 0
    }
    fn add(&mut self, tag: Self) {
        self.0 |= tag.0;
    }
    fn doc_str(self) -> &'static str {
        if self == Self::LAW {
            "law"
        } else if self == Self::PROPHETIC {
            "prophetic"
        } else {
            "sealed"
        }
    }
}

impl ToTokens for LogicTag {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(quote!(#[creusot::decl::logic]));
        if self.has(Self::PROPHETIC) {
            tokens.extend(quote!(#[creusot::decl::logic::prophetic]));
        }
        if self.has(Self::SEALED) {
            tokens.extend(quote!(#[creusot::decl::logic::sealed]));
        }
        if self.has(Self::LAW) {
            tokens.extend(quote!(#[creusot::decl::law] #[creusot::decl::no_trigger]));
        }
    }
}

fn logic_sig(mut sig: TraitItemSignature, tags: LogicTag, documentation: TokenStream) -> TS1 {
    let span = sig.span();
    let attrs = std::mem::take(&mut sig.attrs);

    TS1::from(quote_spanned! {span =>
        #tags
        #(#attrs)*
        #documentation
        #sig
    })
}

fn logic_item(log: LogicItem, tags: LogicTag, documentation: TokenStream) -> TS1 {
    let span = log.sig.span();

    let term = log.body;
    let vis = log.vis;
    let def = log.defaultness;
    let sig = log.sig;
    let attrs = log.attrs;
    let req_body = pretyping::encode_block(&term);

    TS1::from(quote_spanned! {span =>
        #tags
        #(#attrs)*
        #documentation
        #vis #def #sig #req_body
    })
}
