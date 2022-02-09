extern crate proc_macro;
use pearlite_syn::*;
use proc_macro::TokenStream as TS1;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};
use std::iter;
use syn::{
    parse::{Parse, Result},
    punctuated::{Pair, Punctuated},
    token::{Brace, Comma, Paren},
    *,
};

mod pretyping;

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
    sig: Signature,
    semi_token: Token![;],
}

impl ToTokens for TraitItemSignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(self.attrs.outer());
        self.sig.to_tokens(tokens);
        self.semi_token.to_tokens(tokens);
    }
}

enum ContractItem {
    Fn(ItemFn),
    TraitSig(TraitItemSignature),
    Closure(ExprClosure),
}

impl ContractItem {
    fn name(&self) -> String {
        match self {
            ContractItem::Fn(i) => i.sig.ident.to_string(),
            ContractItem::TraitSig(tr) => tr.sig.ident.to_string(),
            ContractItem::Closure(_) => "closure".to_string(),
        }
    }
}

impl Parse for ContractItem {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let mut attrs = input.call(Attribute::parse_outer)?;
        // Infalliable, no visibility = inherited
        let vis: Visibility = input.parse()?;
        let sig: Signature = input.parse()?;
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![;]) {
            let semi_token: Token![;] = input.parse()?;
            return Ok(ContractItem::TraitSig(TraitItemSignature { attrs, sig, semi_token }));
        } else if input.peek(Token![|])
            || input.peek(Token![async]) && (input.peek2(Token![|]) || input.peek2(Token![move]))
            || input.peek(Token![static])
            || input.peek(Token![move])
        {
            return Ok(ContractItem::Closure(input.parse()?));
        } else {
            let content;
            let brace_token = braced!(content in input);
            attrs.extend(Attribute::parse_inner(input)?);
            let stmts = content.call(Block::parse_within)?;

            return Ok(ContractItem::Fn(ItemFn {
                attrs,
                vis,
                sig,
                block: Box::new(Block { brace_token, stmts }),
            }));
        }
    }
}

// Generate a token stream for the item representing a specific
// `requires` or `ensures`
fn fn_spec_item2(tag: Ident, result: Option<FnArg>, p: Term) -> TokenStream {
    let req_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #tag });

    quote! {
        #[allow(unused_must_use)]
        let _ =
            #[creusot::no_translate]
            #[creusot::item=#name_tag]
            #[creusot::decl::spec]
            |#result|{ #req_body }
        ;
    }
}

fn sig_spec_item2(tag: Ident, mut sig: Signature, p: Term) -> TokenStream {
    let req_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #tag });
    sig.ident = tag;
    sig.output = parse_quote! { -> bool };

    quote! {
        #[creusot::no_translate]
        #[creusot::item=#name_tag]
        #[creusot::decl::spec]
        #sig { #req_body }
    }
}

#[proc_macro_attribute]
pub fn requires(attr: TS1, tokens: TS1) -> TS1 {
    let item = parse_macro_input!(tokens as ContractItem);
    let term = parse_macro_input!(attr as Term);

    let req_name = generate_unique_ident(&item.name());

    let name_tag = format!("{}", quote! { #req_name });

    match item {
        ContractItem::Fn(mut f) => {
            let requires_tokens = fn_spec_item2(req_name, None, term);

            f.block.stmts.insert(0, Stmt::Item(Item::Verbatim(requires_tokens)));
            TS1::from(quote! {
              #[creusot::spec::requires=#name_tag]
              #f
            })
        }
        ContractItem::TraitSig(s) => {
            let requires_tokens = sig_spec_item2(req_name, s.sig.clone(), term);
            TS1::from(quote! {
              #requires_tokens
              #[creusot::spec::requires=#name_tag]
              #s
            })
        }
        _ => panic!(),
    }
}

#[proc_macro_attribute]
pub fn ensures(attr: TS1, tokens: TS1) -> TS1 {
    let item = parse_macro_input!(tokens as ContractItem);
    let term = parse_macro_input!(attr as Term);

    let ens_name = generate_unique_ident(&item.name());
    let name_tag = format!("{}", quote! { #ens_name });

    match item {
        ContractItem::Fn(mut f) => {
            let result = match f.sig.output {
                ReturnType::Default => parse_quote! { result : () },
                ReturnType::Type(_, ref ty) => parse_quote! { result : #ty },
            };
            let ensures_tokens = fn_spec_item2(ens_name, Some(result), term);

            f.block.stmts.insert(0, Stmt::Item(Item::Verbatim(ensures_tokens)));
            TS1::from(quote! {
                #[creusot::spec::ensures=#name_tag]
                #f
            })
        }
        ContractItem::TraitSig(s) => {
            let result = match s.sig.output {
                ReturnType::Default => parse_quote! { result : () },
                ReturnType::Type(_, ref ty) => parse_quote! { result : #ty },
            };

            let mut sig = s.sig.clone();
            sig.inputs.push(result);
            let ensures_tokens = sig_spec_item2(ens_name, sig, term);
            TS1::from(quote! {
              #ensures_tokens
              #[creusot::spec::ensures=#name_tag]
              #s
            })
        }
        _ => panic!(),
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
    // var_sig.output = parse_quote! { -> impl creusot_contracts::logic::WellFounded };
    let var_body = pretyping::encode_term(p).unwrap();
    let name_tag = format!("{}", quote! { #var_name });

    let variant_tokens = quote! {
        #[allow(unused_must_use)]
        let _ =
            #[creusot::no_translate]
            #[creusot::item=#name_tag]
            #[creusot::decl::spec]
            ||{ creusot_contracts::stubs::variant_check(#var_body) }
        ;
    };

    f.block.stmts.insert(0, Stmt::Item(Item::Verbatim(variant_tokens)));

    // TODO: Parse and pass down all the function's arguments.
    Ok(TS1::from(quote! {
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

    let assert_body = pretyping::encode_block(assert.0).unwrap();

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
        let sig: Signature = input.parse()?;
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![;]) {
            let semi_token: Token![;] = input.parse()?;
            return Ok(LogicInput::Sig(TraitItemSignature { attrs, sig, semi_token }));
        } else {
            let body;
            let brace_token = braced!(body in input);
            let stmts = body.call(TBlock::parse_within)?;

            Ok(LogicInput::Item(LogicItem {
                vis,
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

    let req_body = pretyping::encode_block(*term).unwrap();

    TS1::from(quote! {
        #[creusot::decl::logic]
        #(#attrs)*
        #vis #sig {
            #req_body
        }
    })
}

#[proc_macro_attribute]
pub fn law(_: TS1, tokens: TS1) -> TS1 {
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::law]
        #[logic]
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
    TS1::from(quote! {
        #[creusot::decl::predicate]
        #sig
    })
}

fn predicate_item(log: LogicItem) -> TS1 {
    let term = log.body;
    let vis = log.vis;
    let sig = log.sig;
    let attrs = log.attrs;

    let req_body = pretyping::encode_block(*term).unwrap();

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
    // let p: ItemFn = parse_macro_input!(tokens);
    let tokens = TokenStream::from(tokens);
    TS1::from(quote! {
        #[creusot::decl::trusted]
        #tokens
    })
}

#[proc_macro]
pub fn pearlite(tokens: TS1) -> TS1 {
    let term: Term = parse_macro_input!(tokens);
    TS1::from(pretyping::encode_term(term).unwrap())
}

struct ExternSig {
    attrs: Vec<Attribute>,
    path: Path,
    generics: Generics,
    inputs: Punctuated<FnArg, Comma>,
    output: ReturnType,
}

impl Parse for ExternSig {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs: Vec<Attribute> = Attribute::parse_outer(input)?;
        let _: Token![fn] = input.parse()?;
        // let path = Punctuated::parse_separated_nonempty(input)?;
        let path = Path::parse_mod_style(input)?;
        let mut generics: Generics = input.parse()?;

        let content;
        let _ = parenthesized!(content in input);
        let inputs = Punctuated::parse_terminated(&content)?;

        let output = input.parse()?;
        generics.where_clause = input.parse()?;

        Ok(ExternSig { attrs, path, generics, inputs, output })
    }
}

#[proc_macro]
pub fn extern_spec(tokens: TS1) -> TS1 {
    // TODO: extend to vectors
    let externs: ExternSig = parse_macro_input!(tokens);
    let externs = vec![externs];

    let mut specs = Vec::new();
    for spec in externs {
        let args: Punctuated<Expr, Comma> = spec
            .inputs
            .clone()
            .into_pairs()
            .map(|inp| {
                let (inp, comma) = inp.into_tuple();
                let exp: Expr = match inp {
                    FnArg::Receiver(_) => Expr::Verbatim(quote! { self }),
                    FnArg::Typed(PatType { pat, .. }) => Expr::Verbatim(quote! { #pat }),
                };
                Pair::new(exp, comma)
            })
            .collect();

        let call = ExprCall {
            attrs: Vec::new(),
            func: Box::new(Expr::Path(ExprPath {
                attrs: Vec::new(),
                qself: None,
                path: spec.path,
            })),
            paren_token: Paren { span: Span::call_site() },
            args,
        };

        let ident = generate_unique_ident("extern_spec");
        let sig = Signature {
            constness: None,
            asyncness: None,
            unsafety: None,
            abi: None,
            fn_token: Token![fn](Span::call_site()),
            ident,
            generics: spec.generics,
            paren_token: Paren { span: Span::call_site() },
            inputs: spec.inputs,
            variadic: None,
            output: spec.output,
        };

        specs.push(ItemFn {
            attrs: spec.attrs,
            vis: Visibility::Inherited,
            sig,
            block: Box::new(Block {
                brace_token: Brace { span: Span::call_site() },
                stmts: vec![Stmt::Expr(Expr::Call(call))],
            }),
        });
    }

    TS1::from(quote! {
        #(#[creusot::no_translate]
          #[creusot::extern_spec]
          #specs
        )*
    })
}
