mod display;

use crate::creusot::doc::DocItemName;
use pearlite_syn::term::*;
use proc_macro::{Diagnostic, Level, TokenStream as TS1};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    parse::Parse,
    punctuated::{Pair, Punctuated},
    spanned::Spanned,
    token::{Brace, Colon, Comma, For, Impl, Paren, Plus, Trait, Unsafe},
    visit_mut::VisitMut,
    *,
};

/// The `extern_spec!` macro.
pub fn extern_spec(tokens: TS1) -> TS1 {
    let externs: ExternSpecs = parse_macro_input!(tokens);

    let mut specs = Vec::new();
    let externs = match externs.flatten() {
        Ok(externs) => externs,
        Err(err) => return TS1::from(err.to_compile_error()),
    };

    for spec in externs {
        specs.push(spec.into_tokens());
    }

    TS1::from(quote! {
        #(#specs)*
    })
}

#[derive(Debug)]
struct ExternSpecs(Vec<ExternSpec>);

/// An extern spec is either:
/// - A module of extern specs
/// - A trait spec defining a subset of a trait's methods
/// - An impl spec defining a subset of a type or trait impl's methods
/// - A bare function spec defining a single non-trait or impl function
#[derive(Debug)]
enum ExternSpec {
    Mod(ExternMod),
    Trait(ExternTrait),
    Impl(ExternImpl),
    Fn(ExternMethod),
}

#[derive(Debug)]
struct ExternMod {
    ident: Ident,
    content: Vec<ExternSpec>,
}

#[derive(Debug)]
struct ExternTrait {
    _unsafety: Option<Unsafe>,
    _trait_token: Trait,
    ident: Ident,
    generics: Generics,
    _colon_token: Option<Colon>,
    _supertraits: Punctuated<TypeParamBound, Plus>,
    _brace_token: Brace,
    items: Vec<ExternMethod>,
}

/// An 'impl' block, either for a trait or standalone
#[derive(Debug)]
struct ExternImpl {
    _attrs: Vec<Attribute>,
    _defaultness: Option<token::Default>,
    _unsafety: Option<Unsafe>,
    _impl_token: Impl,
    generics: Generics,
    trait_: Option<(Path, For)>,
    self_ty: Box<Type>,
    brace_token: Brace,
    items: Vec<ExternMethod>,
}

#[derive(Debug)]
struct ExternMethod {
    span: Span,
    attrs: Vec<Attribute>,
    sig: Signature,
    body: std::result::Result<Block, Token![;]>,
}

// Information related to desugaring.

#[derive(Clone, Debug)]
enum TraitOrImpl {
    Trait(Ident, Generics),
    Impl(Box<Type>),
}

#[derive(Clone, Debug)]
struct ImplData {
    self_ty: TraitOrImpl,
    params: Punctuated<GenericParam, Comma>,
    where_clause: Option<Punctuated<WherePredicate, Comma>>,
}

#[derive(Clone, Debug)]
struct FlatSpec {
    span: Span,
    signature: Signature,
    doc_item_name: DocItemName,
    attrs: Vec<Attribute>,
    /// Expression that can be used to refer to the function being specified
    path: ExprPath,
    impl_data: Option<ImplData>,
    body: Option<Block>,
}

impl ExternSpecs {
    fn flatten(self) -> Result<Vec<FlatSpec>> {
        let mut specs = Vec::new();

        for spec in self.0 {
            flatten(
                spec,
                ExprPath {
                    attrs: Vec::new(),
                    qself: None,
                    path: Path { leading_colon: None, segments: Punctuated::new() },
                },
                DocItemName(String::from("extern_spec")),
                None,
                &mut specs,
            )?
        }
        Ok(specs)
    }
}

fn self_escape<T: Parse>(span: Span) -> T {
    parse_quote_spanned! {span=> self_ }
}

fn self_type_escape<T: Parse>(span: Span) -> T {
    parse_quote_spanned! {span=> Self_ }
}

impl FlatSpec {
    fn into_tokens(mut self) -> TokenStream {
        let span = self.span;
        let args: Punctuated<Expr, Comma> = self
            .signature
            .inputs
            .clone()
            .into_pairs()
            .map(|inp| {
                let (inp, comma) = inp.into_tuple();
                let exp: Expr = if let FnArg::Typed(PatType { pat, .. }) = inp {
                    Expr::Verbatim(pat.to_token_stream())
                } else {
                    Expr::Verbatim(self_escape(inp.span()))
                };
                Pair::new(exp, comma)
            })
            .collect();

        let ident = crate::creusot::generate_unique_ident("extern_spec", span);

        let mut replacer;
        if let Some(mut data) = self.impl_data {
            data.params.extend(self.signature.generics.params);
            self.signature.generics.params = data.params;

            if self.signature.generics.where_clause.is_none() {
                self.signature.generics.where_clause = Some(WhereClause {
                    where_token: Default::default(),
                    predicates: Default::default(),
                });
            }

            let where_clause = self.signature.generics.where_clause.as_mut().unwrap();

            if let Some(p) = data.where_clause {
                where_clause.predicates.extend(p)
            };

            let escape = match &data.self_ty {
                TraitOrImpl::Trait(_, _) => SelfTypeKind::Self_,
                TraitOrImpl::Impl(ty) => SelfTypeKind::Type(ty.clone()),
            };
            replacer = SelfTypeEscaper { escape, err: Ok(()) };

            self.signature.inputs.iter_mut().for_each(|input| match input {
                FnArg::Receiver(Receiver { self_token, ty, .. }) => {
                    // An `impl` block may have a `self` reciever, but we should replace it with the actual
                    // underlying type. This constructs the correct replacement for those cases.

                    let mut ty = ty.clone();
                    replacer.visit_type_mut(&mut ty);

                    let self_: Ident = self_escape(self_token.span());

                    *input = FnArg::Typed(PatType {
                        attrs: Vec::new(),
                        pat: parse_quote!(#self_),
                        colon_token: Default::default(),
                        ty,
                    });
                }
                FnArg::Typed(PatType { ty, .. }) => replacer.visit_type_mut(ty),
            });

            replacer.visit_return_type_mut(&mut self.signature.output);

            if let TraitOrImpl::Trait(trait_name, generics) = data.self_ty {
                let selfty = self_type_escape(span);
                where_clause
                    .predicates
                    .push(parse_quote_spanned! {span=> #selfty : ?::core::marker::Sized + #trait_name #generics });

                self.signature.generics.params.insert(0, selfty);

                where_clause.predicates.iter_mut().for_each(|pred| {
                    replacer.visit_where_predicate_mut(pred);
                });
            }

            if let Some(block) = &mut self.body {
                replacer.visit_block_mut(block)
            }
        } else {
            replacer = SelfTypeEscaper { escape: SelfTypeKind::None, err: Ok(()) };
        }

        if let Err(e) = escape_self_in_contracts(&mut self.attrs, &mut replacer) {
            return e.into_compile_error();
        }
        if let Err(e) = replacer.err {
            return e.into_compile_error();
        }

        let sig = Signature {
            constness: None,
            asyncness: None,
            unsafety: self.signature.unsafety,
            abi: None,
            fn_token: Token![fn](self.signature.span()),
            ident,
            generics: self.signature.generics,
            paren_token: Paren::default(),
            inputs: self.signature.inputs,
            variadic: None,
            output: self.signature.output,
        };
        let mut attrs = filter_erasure(&self.attrs);
        let has_erasure = attrs.len() < self.attrs.len();
        attrs.push(parse_quote! { #[allow(dead_code, non_snake_case)] });

        let call = Expr::Call(ExprCall {
            attrs: Vec::new(),
            func: Box::new(Expr::Path(self.path.clone())),
            paren_token: Paren::default(),
            args,
        });

        // If the function was given a body to check, it is generated here.
        let f_with_body = if let Some(mut b) = self.body {
            let attrs = attrs.clone();
            if has_erasure {
                let erasure_stmt = parse_quote! {
                    let _ =
                        #[creusot::no_translate]
                        #[creusot::spec::erasure]
                        || #call;
                };
                b.stmts.insert(0, erasure_stmt);
            }
            escape_self_in_block(&mut b);
            let mut sig = sig.clone();
            sig.ident = Ident::new(&format!("{}_body", self.doc_item_name.0), sig.ident.span());
            Some(ItemFn { attrs, vis: Visibility::Inherited, sig, block: Box::new(b) })
        } else {
            None
        };

        let doc = {
            let mut path = String::new();
            if let Some(qself) = &self.path.qself {
                path.push_str(&format!("{}", display::DisplayType(&qself.ty)));
            }
            if self.path.path.leading_colon.is_none() && self.path.qself.is_some() {
                path.push_str("::");
            }

            path.push_str(&format!("{}", display::DisplayPath(&self.path.path)));
            format!("extern spec for [`{path}`]")
        };
        // only used in documentation
        let f_doc = ItemFn {
            attrs: attrs.clone(),
            vis: parse_quote!(pub),
            sig: {
                let mut sig = sig.clone();
                sig.ident = Ident::new(&self.doc_item_name.0.to_string(), sig.ident.span());
                sig
            },
            block: Box::new(Block { brace_token: Brace(span), stmts: vec![parse_quote!(loop {})] }),
        };

        let block = Block {
            brace_token: Brace(span), // This sets the span of the function's DefId
            stmts: vec![Stmt::Expr(call, None)],
        };
        let f = ItemFn { attrs, vis: Visibility::Inherited, sig, block: Box::new(block) };

        quote_spanned! {span=>
            #[creusot::no_translate] #[creusot::extern_spec]
            #f

            #[cfg(doc)]
            #[doc = #doc]
            #[doc = ""]
            #[doc = "This is not a real function: its only use is for documentation."]
            #[doc = ""]
            #f_doc

            #f_with_body
        }
    }
}

fn filter_erasure(attrs: &[Attribute]) -> Vec<Attribute> {
    attrs
        .iter()
        .filter(|attr| {
            let is_erasure = attr.path().is_ident("erasure");
            if is_erasure && attr.meta.require_path_only().is_err() {
                Diagnostic::spanned(
                    attr.span().unwrap(),
                    Level::Error,
                    "#[erasure] inside `extern_spec!` must not have arguments",
                )
                .emit();
            }
            !is_erasure
        })
        .cloned()
        .collect::<Vec<_>>()
}

enum SelfTypeKind {
    Self_,
    Type(Box<Type>),
    None,
}

struct SelfTypeEscaper {
    escape: SelfTypeKind,
    err: Result<()>,
}

impl SelfTypeEscaper {
    fn visit_struct_path(&mut self, path: &mut Path) {
        if path.segments[0].ident == "Self" {
            match &self.escape {
                SelfTypeKind::None => (),
                SelfTypeKind::Type(box Type::Path(TypePath { path: pathty, .. }))
                    if path.segments.len() == 1 =>
                {
                    *path = pathty.clone()
                }
                SelfTypeKind::Type(_) => {
                    self.err = Err(Error::new(path.segments[0].span(), "Cannot use Self here."))
                }
                SelfTypeKind::Self_ => path.segments[0] = self_type_escape(path.segments[0].span()),
            }
        }
    }
}

impl syn::visit_mut::VisitMut for SelfTypeEscaper {
    fn visit_type_mut(&mut self, ty: &mut Type) {
        if let Type::Path(TypePath { path, .. }) = ty
            && path.segments[0].ident == "Self"
        {
            match &self.escape {
                SelfTypeKind::None => (),
                SelfTypeKind::Type(box escty) if path.segments.len() == 1 => *ty = escty.clone(),
                SelfTypeKind::Type(_) => {
                    self.err = Err(Error::new(path.segments[0].span(), "Cannot use Self here."))
                }
                SelfTypeKind::Self_ => path.segments[0] = self_type_escape(path.segments[0].span()),
            }
        }

        visit_mut::visit_type_mut(self, ty);
    }

    fn visit_expr_struct_mut(&mut self, expr: &mut ExprStruct) {
        self.visit_struct_path(&mut expr.path);
        visit_mut::visit_expr_struct_mut(self, expr);
    }

    fn visit_expr_path_mut(&mut self, expr: &mut ExprPath) {
        if expr.path.segments[0].ident == "Self" {
            let span = expr.path.segments[0].span();
            match &self.escape {
                SelfTypeKind::None => (),
                SelfTypeKind::Type(_) => self.err = Err(Error::new(span, "Cannot use Self here.")),
                SelfTypeKind::Self_ => expr.path.segments[0] = self_type_escape(span),
            }
        }
        visit_mut::visit_expr_path_mut(self, expr);
    }
}

fn escape_self_in_contracts(
    attrs: &mut Vec<Attribute>,
    replacer: &mut SelfTypeEscaper,
) -> Result<()> {
    for attr in attrs {
        if let Some(id) = attr.path().get_ident()
            && (id == "ensures" || id == "requires")
            && let Meta::List(l) = &mut attr.meta
        {
            let tokens = std::mem::take(&mut l.tokens);
            let mut term: Term = syn::parse2(tokens)?;
            escape_self_in_term(&mut term, replacer);
            l.tokens = term.into_token_stream();
        }
    }
    Ok(())
}

fn escape_self_in_block(b: &mut Block) {
    struct BlockSelfRename;
    impl VisitMut for BlockSelfRename {
        fn visit_expr_path_mut(&mut self, i: &mut ExprPath) {
            if i.path.is_ident("self") {
                i.path = self_escape(i.path.span());
            }
        }
    }
    BlockSelfRename.visit_block_mut(b);
}

fn escape_self_in_term(t: &mut Term, replacer: &mut SelfTypeEscaper) {
    match t {
        Term::Array(TermArray { elems, .. }) => {
            for elem in elems {
                escape_self_in_term(elem, replacer)
            }
        }
        Term::Binary(TermBinary { left, right, .. }) => {
            escape_self_in_term(left, replacer);
            escape_self_in_term(right, replacer)
        }
        Term::Block(TermBlock { block, .. }) => escape_self_in_tblock(block, replacer),
        Term::Call(TermCall { func, args, .. }) => {
            escape_self_in_term(func, replacer);
            for arg in args {
                escape_self_in_term(arg, replacer)
            }
        }
        Term::Cast(TermCast { expr, ty, .. }) => {
            replacer.visit_type_mut(ty);
            escape_self_in_term(expr, replacer)
        }
        Term::Field(TermField { base, member, .. }) => {
            replacer.visit_member_mut(member);
            escape_self_in_term(base, replacer)
        }
        Term::Group(TermGroup { expr, .. }) => escape_self_in_term(expr, replacer),
        Term::If(TermIf { cond, then_branch, else_branch, .. }) => {
            escape_self_in_term(cond, replacer);
            escape_self_in_tblock(then_branch, replacer);
            if let Some((_, b)) = else_branch {
                escape_self_in_term(b, replacer);
            }
        }
        Term::Index(TermIndex { expr, index, .. }) => {
            escape_self_in_term(expr, replacer);
            escape_self_in_term(index, replacer);
        }
        Term::Let(TermLet { expr, pat, .. }) => {
            replacer.visit_pat_mut(pat);
            escape_self_in_term(expr, replacer)
        }
        Term::Lit(TermLit { lit }) => replacer.visit_lit_mut(lit),
        Term::Match(TermMatch { expr, arms, .. }) => {
            escape_self_in_term(expr, replacer);
            for arm in arms {
                replacer.visit_pat_mut(&mut arm.pat);
                if let Some(guard) = &mut arm.guard {
                    escape_self_in_term(&mut guard.1, replacer);
                }
                escape_self_in_term(&mut arm.body, replacer)
            }
        }
        Term::MethodCall(TermMethodCall { receiver, turbofish, args, .. }) => {
            escape_self_in_term(receiver, replacer);
            if let Some(turbofish) = turbofish {
                for arg in &mut turbofish.args {
                    match arg {
                        TermGenericMethodArgument::Type(ty) => replacer.visit_type_mut(ty),
                        TermGenericMethodArgument::Const(term) => {
                            escape_self_in_term(term, replacer)
                        }
                    }
                }
            }
            for arg in args {
                escape_self_in_term(arg, replacer)
            }
        }
        Term::Paren(TermParen { expr, .. }) => escape_self_in_term(expr, replacer),
        Term::Path(TermPath { inner }) => {
            if inner.path.get_ident().is_some_and(|id| id == "self") {
                inner.path = self_escape(inner.span());
            } else {
                replacer.visit_expr_path_mut(inner)
            }
        }
        Term::Range(TermRange { from, to, .. }) => {
            if let Some(from) = from {
                escape_self_in_term(from, replacer);
            }
            if let Some(to) = to {
                escape_self_in_term(to, replacer);
            }
        }
        Term::Reference(TermReference { expr, .. }) => escape_self_in_term(expr, replacer),
        Term::Repeat(TermRepeat { expr, len, .. }) => {
            escape_self_in_term(expr, replacer);
            escape_self_in_term(len, replacer);
        }
        Term::Struct(TermStruct { path, fields, rest, .. }) => {
            replacer.visit_struct_path(path);
            for field in fields {
                replacer.visit_member_mut(&mut field.member);
                escape_self_in_term(&mut field.expr, replacer)
            }
            if let Some(t) = rest {
                escape_self_in_term(t, replacer)
            }
        }
        Term::Tuple(TermTuple { elems, .. }) => {
            for elem in elems {
                escape_self_in_term(elem, replacer)
            }
        }
        Term::Type(TermType { expr, ty, .. }) => {
            escape_self_in_term(expr, replacer);
            replacer.visit_type_mut(ty)
        }
        Term::Unary(TermUnary { expr, .. }) => escape_self_in_term(expr, replacer),
        Term::Final(TermFinal { term, .. }) => escape_self_in_term(term, replacer),
        Term::View(TermView { term, .. }) => escape_self_in_term(term, replacer),
        Term::Impl(TermImpl { hyp, cons, .. }) => {
            escape_self_in_term(hyp, replacer);
            escape_self_in_term(cons, replacer)
        }
        Term::Quant(TermQuant { args, trigger, term, .. }) => {
            for arg in args.iter_mut() {
                if let Some((_, box ty)) = &mut arg.ty {
                    replacer.visit_type_mut(ty)
                }
            }
            for t in trigger.iter_mut().flat_map(|tr| tr.terms.iter_mut()) {
                escape_self_in_term(t, replacer)
            }
            escape_self_in_term(term, replacer)
        }
        Term::Dead(TermDead { .. }) => {}
        Term::Pearlite(TermPearlite { block, .. }) => escape_self_in_tblock(block, replacer),
        Term::ProofAssert(TermProofAssert { block, .. }) => escape_self_in_tblock(block, replacer),
        Term::Seq(TermSeq { terms, .. }) => {
            for term in terms {
                escape_self_in_term(term, replacer)
            }
        }
        Term::Closure(TermClosure { inputs, output, body, .. }) => {
            for input in inputs.iter_mut() {
                replacer.visit_pat_mut(input)
            }
            replacer.visit_return_type_mut(output);
            escape_self_in_term(body, replacer)
        }
        Term::__Nonexhaustive => {}
    }
}

fn escape_self_in_tblock(t: &mut TBlock, replacer: &mut SelfTypeEscaper) {
    for s in &mut t.stmts {
        match s {
            TermStmt::Local(TLocal { init: Some((_, t)), .. }) => escape_self_in_term(t, replacer),
            TermStmt::Expr(t) => escape_self_in_term(t, replacer),
            TermStmt::Semi(t, _) => escape_self_in_term(t, replacer),
            _ => {}
        }
    }
}

fn flatten(
    ex: ExternSpec,
    mut prefix: ExprPath,
    // Generated name for the extern spec body/the docmentation
    mut item_name: DocItemName,
    impl_data: Option<ImplData>,
    flat: &mut Vec<FlatSpec>,
) -> Result<()> {
    match ex {
        ExternSpec::Mod(modl) => {
            if prefix.path.leading_colon.is_none() {
                prefix.path.leading_colon = Some(Default::default());
            }
            item_name.add_ident(&modl.ident);
            prefix
                .path
                .segments
                .push(PathSegment { ident: modl.ident, arguments: PathArguments::None });
            for item in modl.content {
                flatten(item, prefix.clone(), item_name.clone(), None, flat)?;
            }
        }
        ExternSpec::Trait(trait_) => {
            if prefix.path.leading_colon.is_none() {
                prefix.path.leading_colon = Some(Default::default());
            }
            prefix
                .path
                .segments
                .push(PathSegment { ident: trait_.ident.clone(), arguments: PathArguments::None });

            item_name.add_ident(&trait_.ident);
            item_name.add_generics(&trait_.generics);
            for item in trait_.items {
                flatten(
                    ExternSpec::Fn(item),
                    prefix.clone(),
                    item_name.clone(),
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
            if prefix.path.leading_colon.is_none() {
                prefix.path.leading_colon = Some(Default::default());
            }
            let mut ty = impl_.self_ty;
            while let Type::Group(TypeGroup { elem, .. }) | Type::Paren(TypeParen { elem, .. }) =
                *ty
            {
                ty = elem
            }
            if prefix.path.segments.is_empty() {
                prefix.qself = Some(QSelf {
                    lt_token: Default::default(),
                    ty: ty.clone(),
                    position: 0,
                    as_token: None,
                    gt_token: Default::default(),
                });
            } else if let Type::Path(ty_path) = &*ty
                && ty_path.path.segments.len() == 1
            {
                let mut segment = ty_path.path.segments[0].clone();
                if let PathArguments::AngleBracketed(arg) = &mut segment.arguments {
                    arg.colon2_token = Some(Default::default());
                }

                prefix.path.segments.push(segment);
            } else {
                return Err(Error::new(impl_.brace_token.span.join(), "unsupported form of impl"));
            }

            item_name.add_generics(&impl_.generics);
            if let Some((trait_, _)) = &impl_.trait_ {
                item_name.add_path(trait_);
            }
            item_name.add_type(&ty);
            for item in impl_.items {
                flatten(
                    ExternSpec::Fn(item),
                    prefix.clone(),
                    item_name.clone(),
                    Some(ImplData {
                        self_ty: TraitOrImpl::Impl(ty.clone()),
                        params: impl_.generics.params.clone(),
                        where_clause: impl_.generics.where_clause.clone().map(|w| w.predicates),
                    }),
                    flat,
                )?;
            }
        }
        ExternSpec::Fn(fun) => {
            prefix.path.segments.push(PathSegment {
                ident: fun.sig.ident.clone(),
                arguments: generic_arguments(&fun.sig),
            });
            item_name.add_ident(&fun.sig.ident);
            flat.push(FlatSpec {
                span: fun.span,
                signature: fun.sig,
                doc_item_name: item_name,
                attrs: fun.attrs,
                path: prefix,
                impl_data,
                body: fun.body.ok(),
            })
        }
    }
    Ok(())
}

fn generic_arguments(sig: &Signature) -> PathArguments {
    generic_arguments_opt(&sig.generics).unwrap_or(PathArguments::None)
}

fn generic_arguments_opt(generics: &Generics) -> Option<PathArguments> {
    Some(PathArguments::AngleBracketed(AngleBracketedGenericArguments {
        colon2_token: None,
        lt_token: generics.lt_token?,
        args: generics.params.iter().filter_map(param_to_argument).collect(),
        gt_token: generics.gt_token?,
    }))
}

fn param_to_argument(t: &GenericParam) -> Option<GenericArgument> {
    match t {
        GenericParam::Lifetime(_) => None, // cannot specify lifetime arguments explicitly if late bound lifetime parameters are present
        GenericParam::Type(t) => Some(GenericArgument::Type(Type::Path(TypePath {
            qself: None,
            path: t.ident.clone().into(),
        }))),
        GenericParam::Const(c) => Some(GenericArgument::Const(Expr::Path(ExprPath {
            attrs: vec![],
            qself: None,
            path: c.ident.clone().into(),
        }))),
    }
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
        } else if lookahead.peek(Token![fn])
            || (lookahead.peek(Token![unsafe]) && input.peek2(Token![fn]))
        {
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
            _unsafety: unsafety,
            _trait_token: trait_token,
            ident,
            generics,
            _colon_token: colon_token,
            _supertraits: supertraits,
            _brace_token: brace_token,
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
        let self_ty: Box<Type>;
        let trait_;

        let is_impl_for = input.peek(Token![for]);
        if is_impl_for {
            let for_token: Token![for] = input.parse()?;
            let mut first_ty_ref = &first_ty;
            while let Type::Group(TypeGroup { elem, .. }) | Type::Paren(TypeParen { elem, .. }) =
                first_ty_ref
            {
                first_ty_ref = elem;
            }
            if let Type::Path(_) = first_ty_ref {
                while let Type::Group(TypeGroup { elem, .. })
                | Type::Paren(TypeParen { elem, .. }) = first_ty
                {
                    first_ty = *elem;
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
            self_ty = Box::new(first_ty);
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
            _attrs: attrs,
            _defaultness: defaultness,
            _unsafety: unsafety,
            _impl_token: impl_token,
            generics,
            trait_,
            self_ty,
            brace_token,
            items,
        })
    }
}

impl Parse for ExternMethod {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let span = input.span();
        let attrs = input.call(Attribute::parse_outer)?;
        let sig: Signature = input.parse()?;

        let body =
            if let Ok(semi) = input.parse::<Token![;]>() { Err(semi) } else { Ok(input.parse()?) };

        Ok(ExternMethod { span, attrs, sig, body })
    }
}
