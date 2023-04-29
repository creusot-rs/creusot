use pearlite_syn::term::*;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
    parse::Parse,
    punctuated::{Pair, Punctuated},
    spanned::Spanned,
    token::{Brace, Colon, Comma, For, Impl, Paren, Plus, Semi, Trait, Unsafe},
    visit_mut::VisitMut,
    *,
};

use crate::generate_unique_ident;

pub struct ExternSpecs(Vec<ExternSpec>);

// An extern spec is either:
// - A module of extern specs
// - A trait spec defining a subset of a trait's methods
// - An impl spec defining a subset of a type or trait impl's methods
// - A bare function spec defining a single non-trait or impl function
pub enum ExternSpec {
    Mod(ExternMod),
    Trait(ExternTrait),
    Impl(ExternImpl),
    Fn(ExternMethod),
}

pub struct ExternMod {
    ident: Ident,
    content: Vec<ExternSpec>,
}
pub struct ExternTrait {
    pub unsafety: Option<Unsafe>,
    pub trait_token: Trait,
    pub ident: Ident,
    pub generics: Generics,
    pub colon_token: Option<Colon>,
    pub supertraits: Punctuated<TypeParamBound, Plus>,
    pub brace_token: Brace,
    pub items: Vec<ExternMethod>,
}

pub struct ExternImpl {
    pub attrs: Vec<Attribute>,
    pub defaultness: Option<token::Default>,
    pub unsafety: Option<Unsafe>,
    pub impl_token: Impl,
    pub generics: Generics,
    pub trait_: Option<(Path, For)>,
    pub self_ty: Box<Type>,
    pub brace_token: Brace,
    pub items: Vec<ExternMethod>,
}
pub struct ExternMethod {
    pub attrs: Vec<Attribute>,
    pub sig: Signature,
    pub semi_token: Option<Semi>,
}

// Information related to desugaring.

enum TraitOrImpl {
    Trait(Ident, Generics),
    Impl(Type),
}

struct ImplData {
    self_ty: TraitOrImpl,
    params: Punctuated<GenericParam, Comma>,
    where_clause: Option<Punctuated<WherePredicate, Comma>>,
}

pub struct FlatSpec {
    span: Span,
    attrs: Vec<Attribute>,
    path: ExprPath,
    generics: Generics,
    inputs: Punctuated<FnArg, Comma>,
    output: ReturnType,
    impl_data: Option<ImplData>,
}

impl ExternSpecs {
    pub fn flatten(self) -> Result<Vec<FlatSpec>> {
        let mut specs = Vec::new();

        for spec in self.0 {
            flatten(
                spec,
                ExprPath {
                    attrs: Vec::new(),
                    qself: None,
                    path: Path {
                        leading_colon: Some(Default::default()),
                        segments: Punctuated::new(),
                    },
                },
                None,
                &mut specs,
            )?
        }
        Ok(specs)
    }
}

impl TraitOrImpl {
    fn self_ty(&self) -> Type {
        match self {
            TraitOrImpl::Trait(_, _) => parse_quote! { Self_ },
            TraitOrImpl::Impl(ty) => ty.clone(),
        }
    }
}

impl FlatSpec {
    pub fn to_tokens(mut self) -> TokenStream {
        let err = escape_self_in_contracts(&mut self.attrs);
        if let Err(e) = err {
            return e.into_compile_error();
        }
        let args: Punctuated<Expr, Comma> = self
            .inputs
            .clone()
            .into_pairs()
            .map(|inp| {
                let (inp, comma) = inp.into_tuple();
                let exp: Expr = if let FnArg::Typed(PatType { pat, .. }) = inp {
                    Expr::Verbatim(quote! { #pat })
                } else {
                    Expr::Verbatim(quote! { self_ })
                };
                Pair::new(exp, comma)
            })
            .collect();

        let call = ExprCall {
            attrs: Vec::new(),
            func: Box::new(Expr::Path(self.path.clone())),
            paren_token: Paren::default(),
            args,
        };

        let ident = generate_unique_ident("extern_spec");

        if let Some(mut data) = self.impl_data {
            data.params.extend(self.generics.params);
            self.generics.params = data.params;

            if self.generics.where_clause.is_none() {
                self.generics.where_clause = Some(WhereClause {
                    where_token: Default::default(),
                    predicates: Default::default(),
                });
            }

            let where_clause = self.generics.where_clause.as_mut().unwrap();

            if let Some(p) = data.where_clause {
                where_clause.predicates.extend(p)
            };

            let self_ty = data.self_ty.self_ty();
            let mut replacer = SelfEscape { self_ty };

            self.inputs.iter_mut().for_each(|input| match input {
                FnArg::Receiver(Receiver { reference, mutability, .. }) => {
                    // An `impl` block may have a `self` reciever, but we should replace it with the actual
                    // underlying type. This constructs the correct replacement for those cases.
                    let mut self_ty = replacer.self_ty.clone();
                    if let Some((_, l)) = reference {
                        self_ty = parse_quote! { & #l #mutability #self_ty};
                    };
                    *input = FnArg::Typed(PatType {
                        attrs: Vec::new(),
                        pat: parse_quote! { self_ },
                        colon_token: Default::default(),
                        ty: Box::new(self_ty),
                    });
                }
                FnArg::Typed(PatType { ty, .. }) => replacer.visit_type_mut(ty),
            });

            replacer.visit_return_type_mut(&mut self.output);

            match data.self_ty {
                TraitOrImpl::Trait(trait_name, generics) => {
                    where_clause.predicates.push(parse_quote! { Self_ : #trait_name #generics });

                    self.generics.params.insert(0, parse_quote! { Self_ });

                    where_clause.predicates.iter_mut().for_each(|pred| {
                        replacer.visit_where_predicate_mut(pred);
                    });
                }
                _ => {}
            }
        }

        let sig = Signature {
            constness: None,
            asyncness: None,
            unsafety: None,
            abi: None,
            fn_token: Token![fn](self.span),
            ident,
            generics: self.generics,
            paren_token: Paren::default(),
            inputs: self.inputs,
            variadic: None,
            output: self.output,
        };

        let f = ItemFn {
            attrs: self.attrs,
            vis: Visibility::Inherited,
            sig,
            block: Box::new(Block {
                brace_token: Brace::default(),
                stmts: vec![Stmt::Expr(Expr::Call(call), None)],
            }),
        };

        quote! { #[allow(dead_code)] #f }
    }
}

struct SelfEscape {
    self_ty: Type,
}

impl syn::visit_mut::VisitMut for SelfEscape {
    fn visit_type_mut(&mut self, ty: &mut Type) {
        match ty {
            Type::Path(TypePath { path, .. }) => {
                if path.segments[0].ident == "Self" {
                    if self.self_ty == parse_quote! { Self_ } {
                        let mut ident: Ident = parse_quote! { Self_ };
                        ident.set_span(path.segments[0].ident.span());
                        path.segments[0].ident = ident;
                    } else {
                        *ty = self.self_ty.clone();
                    }
                }
            }
            _ => {}
        }

        visit_mut::visit_type_mut(self, ty);
    }
}

fn escape_self_in_contracts(attrs: &mut Vec<Attribute>) -> Result<()> {
    for attr in attrs {
        if let Some(id) = attr.path().get_ident() {
            if id == "ensures" || id == "requires" {
                match &mut attr.meta {
                    Meta::List(l) => {
                        let tokens = std::mem::take(&mut l.tokens);
                        let mut term: Term = syn::parse2(tokens)?;
                        escape_self_in_term(&mut term);
                        l.tokens = term.into_token_stream();
                    }
                    _ => (),
                }
            }
        }
    }
    Ok(())
}

fn escape_self_in_term(t: &mut Term) {
    match t {
        Term::Macro(_) => {}
        Term::Array(TermArray { elems, .. }) => {
            for elem in elems {
                escape_self_in_term(elem)
            }
        }
        Term::Binary(TermBinary { left, right, .. }) => {
            escape_self_in_term(left);
            escape_self_in_term(right);
        }
        Term::Block(TermBlock { block, .. }) => escape_self_in_tblock(block),
        Term::Call(TermCall { func, args, .. }) => {
            escape_self_in_term(func);
            for arg in args {
                escape_self_in_term(arg)
            }
        }
        Term::Cast(TermCast { expr, .. }) => {
            escape_self_in_term(expr);
        }
        Term::Field(TermField { base, .. }) => escape_self_in_term(base),
        Term::Group(TermGroup { expr, .. }) => {
            escape_self_in_term(expr);
        }
        Term::If(TermIf { cond, then_branch, else_branch, .. }) => {
            escape_self_in_term(cond);
            escape_self_in_tblock(then_branch);
            if let Some((_, b)) = else_branch {
                escape_self_in_term(b);
            }
        }
        Term::Index(TermIndex { expr, index, .. }) => {
            escape_self_in_term(expr);
            escape_self_in_term(index);
        }
        Term::Let(TermLet { expr, .. }) => {
            escape_self_in_term(expr);
        }
        Term::Match(TermMatch { expr, arms, .. }) => {
            escape_self_in_term(expr);
            for arm in arms {
                escape_self_in_term(&mut arm.body)
            }
        }
        Term::MethodCall(TermMethodCall { receiver, args, .. }) => {
            escape_self_in_term(receiver);
            for arg in args {
                escape_self_in_term(arg)
            }
        }
        Term::Paren(TermParen { expr, .. }) => {
            escape_self_in_term(expr);
        }
        Term::Path(TermPath { inner }) => {
            if let Some(id) = inner.path.get_ident() {
                if id == "self" {
                    inner.path = parse_quote! { self_ };
                }
            }
        }
        Term::Range(TermRange { from, to, .. }) => {
            if let Some(from) = from {
                escape_self_in_term(from);
            }
            if let Some(to) = to {
                escape_self_in_term(to);
            }
        }
        Term::Repeat(TermRepeat { expr, len, .. }) => {
            escape_self_in_term(expr);
            escape_self_in_term(len);
        }
        Term::Struct(TermStruct { fields, rest, .. }) => {
            for field in fields {
                escape_self_in_term(&mut field.expr)
            }
            if let Some(t) = rest {
                escape_self_in_term(t)
            }
        }
        Term::Tuple(TermTuple { elems, .. }) => {
            for elem in elems {
                escape_self_in_term(elem)
            }
        }
        Term::Type(TermType { expr, .. }) => {
            escape_self_in_term(expr);
        }
        Term::Unary(TermUnary { expr, .. }) => {
            escape_self_in_term(expr);
        }
        Term::Final(TermFinal { term, .. }) => escape_self_in_term(term),
        Term::Model(TermModel { term, .. }) => escape_self_in_term(term),
        Term::LogEq(TermLogEq { lhs, rhs, .. }) => {
            escape_self_in_term(lhs);
            escape_self_in_term(rhs)
        }
        Term::Impl(TermImpl { hyp, cons, .. }) => {
            escape_self_in_term(hyp);
            escape_self_in_term(cons);
        }
        Term::Forall(TermForall { term, .. }) => escape_self_in_term(term),
        Term::Exists(TermExists { term, .. }) => escape_self_in_term(term),
        Term::Absurd(TermAbsurd { .. }) => {}
        Term::Pearlite(TermPearlite { block, .. }) => escape_self_in_tblock(block),
        Term::Lit(TermLit { .. }) => {}
        Term::Verbatim(_) => {}
        Term::Closure(TermClosure { body, .. }) => escape_self_in_term(body),
        Term::__Nonexhaustive => {}
    }
}

fn escape_self_in_tblock(t: &mut TBlock) {
    for s in &mut t.stmts {
        match s {
            TermStmt::Local(TLocal { init: Some((_, t)), .. }) => escape_self_in_term(t),
            TermStmt::Expr(t) => escape_self_in_term(t),
            TermStmt::Semi(t, _) => escape_self_in_term(t),
            _ => {}
        }
    }
}

fn flatten(
    ex: ExternSpec,
    mut prefix: ExprPath,
    impl_data: Option<ImplData>,
    flat: &mut Vec<FlatSpec>,
) -> Result<()> {
    match ex {
        ExternSpec::Mod(modl) => {
            prefix
                .path
                .segments
                .push(PathSegment { ident: modl.ident, arguments: PathArguments::None });

            for item in modl.content {
                flatten(item, prefix.clone(), None, flat)?;
            }
        }
        ExternSpec::Trait(trait_) => {
            prefix
                .path
                .segments
                .push(PathSegment { ident: trait_.ident.clone(), arguments: PathArguments::None });

            for item in trait_.items {
                flatten(
                    ExternSpec::Fn(item),
                    prefix.clone(),
                    Some(ImplData {
                        self_ty: TraitOrImpl::Trait(trait_.ident.clone(), trait_.generics.clone()),
                        params: trait_.generics.params.clone(),
                        where_clause: trait_.generics.where_clause.clone().map(|w| w.predicates),
                    }),
                    flat,
                )?;
            }
        }
        ExternSpec::Impl(impl_) => {
            if prefix.path.segments.is_empty() {
                prefix.qself = Some(QSelf {
                    lt_token: Default::default(),
                    ty: impl_.self_ty.clone(),
                    position: prefix.path.segments.len(),
                    as_token: None,
                    gt_token: Default::default(),
                });
                prefix.path.leading_colon = Some(Default::default());
            } else if let Type::Path(ty_path) = &*impl_.self_ty {
                let mut segment = ty_path.path.segments[0].clone();
                if let PathArguments::AngleBracketed(arg) = &mut segment.arguments {
                    arg.colon2_token = Some(Default::default());
                }

                prefix.path.segments.push(segment);
            } else {
                return Err(Error::new(impl_.brace_token.span.join(), "unsupported form of impl"));
            }

            for item in impl_.items {
                flatten(
                    ExternSpec::Fn(item),
                    prefix.clone(),
                    Some(ImplData {
                        self_ty: TraitOrImpl::Impl(*impl_.self_ty.clone()),
                        params: impl_.generics.params.clone(),
                        where_clause: impl_.generics.where_clause.clone().map(|w| w.predicates),
                    }),
                    flat,
                )?;
            }
        }
        ExternSpec::Fn(fun) => {
            prefix
                .path
                .segments
                .push(PathSegment { ident: fun.sig.ident.clone(), arguments: PathArguments::None });
            flat.push(FlatSpec {
                span: fun.sig.span(),
                attrs: fun.attrs,
                path: prefix,
                impl_data,
                generics: fun.sig.generics,
                inputs: fun.sig.inputs,
                output: fun.sig.output,
            })
        }
    }
    Ok(())
}

impl Parse for ExternSpecs {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let mut externs = Vec::new();
        while !input.is_empty() {
            externs.push(input.parse()?)
        }

        Ok(ExternSpecs(externs))
    }
}

impl Parse for ExternSpec {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;

        let lookahead = input.lookahead1();
        if lookahead.peek(Token![mod]) {
            Ok(ExternSpec::Mod(input.parse()?))
        } else if lookahead.peek(Token![impl]) {
            Ok(ExternSpec::Impl(input.parse()?))
        } else if lookahead.peek(Token![trait]) {
            Ok(ExternSpec::Trait(input.parse()?))
        } else if lookahead.peek(Token![fn]) {
            let mut f: ExternMethod = input.parse()?;
            f.attrs.extend(attrs);
            Ok(ExternSpec::Fn(f))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for ExternMod {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let _mod_token: Token![mod] = input.parse()?;
        let ident: Ident = input.parse()?;
        let content;
        let _brace_token = braced!(content in input);
        let mut items = Vec::new();
        while !content.is_empty() {
            items.push(content.parse()?);
        }

        Ok(ExternMod { ident, content: items })
    }
}

impl Parse for ExternTrait {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let unsafety: Option<Token![unsafe]> = input.parse()?;
        let trait_token: Token![trait] = input.parse()?;
        let ident: Ident = input.parse()?;
        let mut generics: Generics = input.parse()?;

        let colon_token: Option<Token![:]> = input.parse()?;

        let mut supertraits = Punctuated::new();
        if colon_token.is_some() {
            loop {
                if input.peek(Token![where]) || input.peek(token::Brace) {
                    break;
                }
                supertraits.push_value(input.parse()?);
                if input.peek(Token![where]) || input.peek(token::Brace) {
                    break;
                }
                supertraits.push_punct(input.parse()?);
            }
        }

        generics.where_clause = input.parse()?;

        let content;
        let brace_token = braced!(content in input);
        let mut items = Vec::new();
        while !content.is_empty() {
            items.push(content.parse()?);
        }

        Ok(ExternTrait {
            unsafety,
            trait_token,
            ident,
            generics,
            colon_token,
            supertraits,
            brace_token,
            items,
        })
    }
}

impl Parse for ExternImpl {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let defaultness: Option<Token![default]> = input.parse()?;
        let unsafety: Option<Token![unsafe]> = input.parse()?;
        let impl_token: Token![impl] = input.parse()?;

        let has_generics = input.peek(Token![<])
            && (input.peek2(Token![>])
                || input.peek2(Token![#])
                || (input.peek2(Ident) || input.peek2(Lifetime))
                    && (input.peek3(Token![:])
                        || input.peek3(Token![,])
                        || input.peek3(Token![>])
                        || input.peek3(Token![=]))
                || input.peek2(Token![const]));
        let mut generics: Generics =
            if has_generics { input.parse()? } else { Generics::default() };

        let is_const_impl =
            input.peek(Token![const]) || input.peek(Token![?]) && input.peek2(Token![const]);
        if is_const_impl {
            return Err(Error::new(input.span(), "cannot use const impls in `extern_spec!`"));
        }

        if input.peek(Token![!]) && !input.peek2(token::Brace) {
            return Err(Error::new(input.span(), "cannot use negative impls in `extern_spec!`"));
        };

        let first_ty_span = input.span();
        let mut first_ty: Type = input.parse()?;
        let self_ty: Type;
        let trait_;

        let is_impl_for = input.peek(Token![for]);
        if is_impl_for {
            let for_token: Token![for] = input.parse()?;
            let mut first_ty_ref = &first_ty;
            while let Type::Group(ty) = first_ty_ref {
                first_ty_ref = &ty.elem;
            }
            if let Type::Path(_) = first_ty_ref {
                while let Type::Group(ty) = first_ty {
                    first_ty = *ty.elem;
                }
                if let Type::Path(TypePath { qself: None, path }) = first_ty {
                    trait_ = Some((path, for_token));
                } else {
                    unreachable!();
                }
            } else {
                trait_ = None;
            }
            self_ty = input.parse()?;
        } else {
            trait_ = None;
            self_ty = first_ty;
        }

        generics.where_clause = input.parse()?;

        let content;
        let brace_token = braced!(content in input);

        let mut items = Vec::new();
        while !content.is_empty() {
            items.push(content.parse()?);
        }
        if is_impl_for && trait_.is_none() {
            return Err(Error::new(first_ty_span, "unexpected type in trait declaration"));
        }

        Ok(ExternImpl {
            attrs,
            defaultness,
            unsafety,
            impl_token,
            generics,
            trait_,
            self_ty: Box::new(self_ty),
            brace_token,
            items,
        })
    }
}

impl Parse for ExternMethod {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let sig: Signature = input.parse()?;

        let semi_token = Some(input.parse()?);

        Ok(ExternMethod { attrs, sig, semi_token })
    }
}
