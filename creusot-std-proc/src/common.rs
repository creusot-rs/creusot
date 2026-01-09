//! Common definitions for `creusot` and `dummy` macro implementations.
use proc_macro2::{Delimiter, Group, Literal, TokenStream, TokenTree};
use quote::{ToTokens, TokenStreamExt, quote_spanned};
use std::iter;
use syn::{
    parse::{Parse, Result},
    visit_mut::{VisitMut, visit_expr_closure_mut},
    *,
};

pub trait FilterAttrs<'a> {
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

pub struct FnOrMethod {
    pub attrs: Vec<Attribute>,
    pub defaultness: Option<Token![default]>,
    pub visibility: Visibility,
    pub sig: Signature,
    pub body: Option<Block>,
    pub semi_token: Option<Token![;]>,
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

impl Parse for FnOrMethod {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
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

        Ok(FnOrMethod {
            attrs,
            defaultness,
            visibility: vis,
            sig,
            body: brace_token.map(|brace_token| Block { brace_token, stmts }),
            semi_token,
        })
    }
}

pub enum ContractSubject {
    FnOrMethod(FnOrMethod),
    Closure(ExprClosure),
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
        let mut item = FnOrMethod::parse(input)?;
        item.attrs = attrs;
        Ok(ContractSubject::FnOrMethod(item))
    }
}

impl ToTokens for ContractSubject {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            ContractSubject::FnOrMethod(tr) => tr.to_tokens(tokens),
            ContractSubject::Closure(closure) => closure.to_tokens(tokens),
        }
    }
}

pub(crate) struct GhostLet {
    pub mutability: Option<syn::Token![mut]>,
    pub var: syn::Ident,
    pub body: syn::Expr,
}

impl syn::parse::Parse for GhostLet {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let mutability = input.parse()?;
        let var = input.parse()?;
        let _: syn::Token![=] = input.parse()?;
        let body = input.parse()?;
        Ok(Self { mutability, var, body })
    }
}

/// Change `xxxint` into `*::creusot_std::logic::Int::new(xxx)`.
pub(crate) fn ghost_int_lit_suffix(tokens: TokenStream) -> TokenStream {
    tokens
        .into_iter()
        .map(|t| match t {
            TokenTree::Group(group) => {
                let mut result = Group::new(group.delimiter(), ghost_int_lit_suffix(group.stream()));
                result.set_span(group.span());
                TokenTree::Group(result)
            }
            TokenTree::Literal(literal) => {
                let lit = literal.to_string();
                if let Some(lit) = lit.strip_suffix("int") {
                    let span = proc_macro2::Span::from(literal.span());
                    let mut lit = Literal::i128_suffixed(lit.parse::<i128>().unwrap());
                    lit.set_span(span);
                    let mut group = Group::new(
                        Delimiter::None,
                        quote_spanned!(span => ::creusot_std::ghost::Ghost::into_inner(::creusot_std::logic::Int::new(#lit))).into(),
                    );
                    group.set_span(literal.span());
                    TokenTree::Group(group)
                } else {
                    TokenTree::Literal(literal)
                }
            }
            TokenTree::Ident(_) | TokenTree::Punct(_) => t,
        })
        .collect()
}

pub(crate) struct GhostClosuresVisitor;

impl VisitMut for GhostClosuresVisitor {
    fn visit_expr_closure_mut(&mut self, i: &mut ExprClosure) {
        let attr: Attribute = parse_quote!(#[check(ghost)]);
        i.attrs.push(attr);
        visit_expr_closure_mut(self, i);
    }
}
