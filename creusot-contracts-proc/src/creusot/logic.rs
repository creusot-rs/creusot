//! Macros for defining logical functions

use super::{
    doc::{self, document_spec},
    pretyping,
};
use crate::common::FilterAttrs as _;
use pearlite_syn::TBlock;
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, TokenStreamExt as _, quote, quote_spanned};
use syn::{
    Attribute, Error, Ident, Item, Result, Signature, Token, VisRestricted, Visibility, braced,
    parenthesized,
    parse::{self, Parse},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    spanned::Spanned as _,
};

pub fn logic(tags: TS1, tokens: TS1) -> TS1 {
    let tags_span = TokenStream::from(tags.clone()).span();
    let tags_idents =
        parse_macro_input!(tags with Punctuated<LogicTag, Token![,]>::parse_terminated);
    let mut tags = LogicTags::default();
    for tag in tags_idents {
        match tag {
            LogicTag::Mode(logic_mode) => {
                if !tags.modes.add(logic_mode) {
                    return syn::Error::new(
                        tags_span,
                        format!("`{}` can only be specified once.", logic_mode.doc_str()),
                    )
                    .into_compile_error()
                    .into();
                }
            }
            LogicTag::Open(visibility) => {
                if tags.open.is_some() {
                    return syn::Error::new(tags_span, "`open` can only be specified once.")
                        .into_compile_error()
                        .into();
                }
                tags.open = Some(visibility);
            }
        }
    }
    let mut log = parse_macro_input!(tokens as LogicInput);

    if let Some(vis) = &tags.open {
        let open_name =
            crate::creusot::generate_unique_ident(&log.name().to_string(), Span::call_site());
        let name_tag = open_name.to_string();
        let open_tokens = quote! {
            #[creusot::no_translate]
            #[creusot::item=#name_tag]
            #vis fn #open_name() {}
        };
        match &mut log {
            LogicInput::Item(logic_item) => {
                logic_item
                    .body
                    .stmts
                    .insert(0, pearlite_syn::TermStmt::Item(Item::Verbatim(open_tokens)));
                logic_item.attrs.push(parse_quote!(#[creusot::clause::open=#name_tag]))
            }
            LogicInput::Sig(_) => {
                return Error::new(Span::call_site(), "Cannot mark trait item signature as open")
                    .to_compile_error()
                    .into();
            }
        }
    }

    let mut doc_str = "logic".to_string();
    if !tags.modes.is_empty() {
        doc_str.push('(');
        let mut comma = false;
        for tag in [LogicMode::LAW, LogicMode::PROPHETIC, LogicMode::SEALED] {
            if tags.modes.has(tag) {
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
        if tags.open.is_some() { log.logic_body() } else { doc::LogicBody::None },
    );

    match log {
        LogicInput::Item(log) => logic_item(log, tags.modes, documentation),
        LogicInput::Sig(sig) => logic_sig(sig, tags.modes, documentation),
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

    fn name(&self) -> &Ident {
        match self {
            LogicInput::Item(logic_item) => &logic_item.sig.ident,
            LogicInput::Sig(trait_item_signature) => &trait_item_signature.sig.ident,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LogicTags {
    modes: LogicMode,
    open: Option<Visibility>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum LogicTag {
    Mode(LogicMode),
    Open(Visibility),
}

impl Parse for LogicTag {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let ident: Ident = input.parse()?;
        if ident == "law" {
            Ok(Self::Mode(LogicMode::LAW))
        } else if ident == "prophetic" {
            Ok(Self::Mode(LogicMode::PROPHETIC))
        } else if ident == "sealed" {
            Ok(Self::Mode(LogicMode::SEALED))
        } else if ident == "open" {
            if input.is_empty() || input.peek(Token![,]) {
                return Ok(Self::Open(Visibility::Public(Default::default())));
            }
            let vis;
            Ok(Self::Open(Visibility::Restricted(VisRestricted {
                pub_token: Default::default(),
                paren_token: parenthesized!(vis in input),
                in_token: None,
                path: vis.parse()?,
            })))
        } else {
            Err(syn::Error::new(
                ident.span(),
                "unsupported modifier. The only supported modifiers are `open`, `prophetic`, `law` and `sealed`",
            ))
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct LogicMode(u8);

impl LogicMode {
    const LAW: Self = Self(1);
    const PROPHETIC: Self = Self(2);
    const SEALED: Self = Self(4);

    fn has(self, tag: Self) -> bool {
        self.0 & tag.0 > 0
    }
    fn is_empty(self) -> bool {
        self.0 == 0
    }
    /// Returns `true` if `self` did _not_ already contain `tag`.
    fn add(&mut self, tag: Self) -> bool {
        let had = self.0 & tag.0 > 0;
        self.0 |= tag.0;
        !had
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

impl ToTokens for LogicMode {
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

fn logic_sig(mut sig: TraitItemSignature, tags: LogicMode, documentation: TokenStream) -> TS1 {
    let span = sig.span();
    let attrs = std::mem::take(&mut sig.attrs);

    TS1::from(quote_spanned! {span =>
        #tags
        #(#attrs)*
        #documentation
        #sig
    })
}

fn logic_item(log: LogicItem, tags: LogicMode, documentation: TokenStream) -> TS1 {
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
