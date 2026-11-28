use super::doc;
use crate::common::FnOrMethod;
// use proc_macro::{Diagnostic, Level};
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream as TS2};
// use quote::{ToTokens, quote_spanned};
use quote::quote;
// use syn::{Pat, PathArguments, Type, punctuated::Punctuated, spanned::Spanned as _, token::Comma};
use syn::{
    ExprPath, GenericArgument, GenericParam, Generics, LifetimeParam, Path, PathArguments, QSelf,
    Stmt, Token, Type, TypeParam, TypePath, WhereClause,
    parse::{Error, Parse, ParseStream, Result},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
};

impl Parse for ErasureArg {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.parse::<Token![_]>().is_ok() {
            return Ok(ErasureArg::Ghost);
        }
        let kw = input.step(|cursor| {
            let error = || Error::new(Span::call_site(), "");
            let (ident, cursor) = cursor.ident().ok_or_else(error)?;
            if ident.to_string() == "private" {
                Ok((false, cursor))
            } else if ident.to_string() == "from" {
                Ok((true, cursor))
            } else {
                Err(error())
            }
        });
        match kw {
            Err(_) => Ok(ErasureArg::Arg { private: false, path: input.parse()? }),
            Ok(true) => Ok(ErasureArg::FromArg { path: input.parse()? }),
            Ok(false) => Ok(ErasureArg::Arg { private: true, path: input.parse()? }),
        }
    }
}

/// `private #path` or `#path`
/// where `#path` is `(<#type as #trait>)?(#ident::)*#ident`
enum ErasureArg {
    Ghost,
    Arg { private: bool, path: ExprPath },
    FromArg { path: ExprPath },
}

/// There are two variants of this attribute
///
/// ## Variant 1
///
/// ```ignore
/// #[erasure(foo)]
/// fn bar(arg: T) { /* ... */ }
///
/// // expands to
///
/// fn bar(arg: T) {
///   let _ =
///     #[creusot::spec::erasure]
///     || foo(arg);
///   /* ... */
/// }
/// ```
///
/// ## Variant 2
///
/// To allow referring to private functions:
///
/// ```ignore
/// #[erasure(private foo)]
/// fn bar(arg: T) { /* ... */ }
///
/// // expands to
///
/// #[creusot::spec::erasure(foo)]
/// fn bar(arg: T) { /* ... */ }
/// ```
pub(crate) fn erasure(arg: TS1, item: TS1) -> TS1 {
    let doc = doc::document_spec("erasure", doc::LogicBody::term(0, arg.clone()));
    let erasure_arg = parse_macro_input!(arg as ErasureArg);
    let mut item = parse_macro_input!(item as FnOrMethod);
    use ErasureArg::*;
    match erasure_arg {
        Arg { private, path } => {
            if private {
                // Add attribute to the item itself
                item.attrs.push(parse_quote!(#[creusot::spec::erasure(#path)]))
            } else {
                let erasure_gadget: Stmt = parse_quote! {
                    #[allow(let_underscore_drop)]
                    let _ =
                        #[creusot::no_translate]
                        #[creusot::spec::erasure]
                        || #path;
                };
                item.body.as_mut().unwrap().stmts.insert(0, erasure_gadget);
            }
        }
        Ghost => {
            item.attrs.push(parse_quote!(#[creusot::spec::erasure(_)]));
        }
        FromArg { path } => {
            let erasure_gadget: Stmt = parse_quote! {
                #[allow(let_underscore_drop)]
                let _ =
                    #[creusot::no_translate]
                    #[creusot::spec::erasure(from)]
                    || #path;
            };
            item.body.as_mut().unwrap().stmts.insert(0, erasure_gadget);
        }
    }
    insert_doc(item, doc)
}

fn insert_doc(item: FnOrMethod, doc: TS2) -> TS1 {
    let FnOrMethod { attrs, defaultness, visibility, sig, body, semi_token } = item;
    TS1::from(quote! {
        #(#attrs)* #doc
        #defaultness #visibility #sig #body #semi_token
    })
}

/// A declaration in `erase!`.
enum EraseDecl {
    /// `type #source => #target #where_clause`
    Type { source: TypePath, target: Type, where_clause: Option<WhereClause> },
    /// `#binder fn #source => #target #where_clause`, where `#binder` is an optional `for<...>`
    Fn {
        binder: Option<Generics>,
        source: ExprPath,
        target: ExprPath,
        where_clause: Option<WhereClause>,
    },
}

impl Parse for EraseDecl {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![type]) {
            input.parse::<Token![type]>()?;
            let source = input.parse()?;
            input.parse::<Token![=>]>()?;
            let target = input.parse()?;
            let where_clause = input.parse()?;
            Ok(EraseDecl::Type { source, target, where_clause })
        } else if lookahead.peek(Token![fn]) || lookahead.peek(Token![for]) {
            let binder = if input.peek(Token![for]) {
                input.parse::<Token![for]>()?;
                Some(input.parse()?)
            } else {
                None
            };
            input.parse::<Token![fn]>()?;
            let source = input.parse()?;
            input.parse::<Token![=>]>()?;
            let target = input.parse()?;
            let where_clause = input.parse()?;
            Ok(EraseDecl::Fn { binder, source, target, where_clause })
        } else {
            Err(lookahead.error())
        }
    }
}

/// Generic parameters of the gadget function for `type/fn #source => #target #where_clause`:
fn erasure_generics(
    qself: &Option<QSelf>,
    path: &Path,
    where_clause: &Option<WhereClause>,
) -> Generics {
    fn type_param(ty: &Type) -> Option<GenericParam> {
        let Type::Path(TypePath { qself: None, path }) = ty else { return None };
        Some(GenericParam::Type(TypeParam::from(path.get_ident()?.clone())))
    }
    fn path_args(path: &Path) -> impl Iterator<Item = &GenericArgument> {
        path.segments.iter().flat_map(|segment| match &segment.arguments {
            PathArguments::AngleBracketed(args) => args.args.iter().collect(),
            _ => Vec::new(),
        })
    }
    // In `<S<T> as Trait>::f`, `S` is a type (the `Self` of an impl) and `T` is a parameter.
    let qself_args = qself.iter().flat_map(|qself| match &*qself.ty {
        Type::Path(TypePath { qself: None, path }) => path_args(path).collect(),
        _ => Vec::new(),
    });
    let args = qself_args.chain(path_args(path));
    let args = args.filter_map(|arg| match arg {
        GenericArgument::Type(ty) => type_param(ty),
        GenericArgument::Lifetime(lt) if lt.ident != "_" && lt.ident != "static" => {
            Some(GenericParam::Lifetime(LifetimeParam::new(lt.clone())))
        }
        _ => None,
    });
    Generics {
        lt_token: Some(Default::default()),
        params: args.collect(),
        gt_token: Some(Default::default()),
        where_clause: where_clause.clone(),
    }
}

/// A `;`-separated list of erasure declarations.
///
/// `type A<T> => B<T> where T: U` expands to
///
/// ```ignore
/// const _: () = {
///    #[creusot::no_translate]
///    #[creusot::spec::erasure_type]
///    fn _erasure<T>(_: A<T>, _: B<T>) where T: U {}
/// };
/// ```
///
/// `fn A::<T>::f::<U> => B::<T>::g::<U> where T: Bound`
/// (equivalent to `#[erasure(B::<T>::g::<U>)]` on `A::<T>::f`) expands to
///
/// ```ignore
/// const _: () = {
///    #[creusot::no_translate]
///    #[creusot::spec::erasure_fn]
///    fn _erasure<T, U>() where T: Bound {
///        let _ = (A::<T>::f::<U>, B::<T>::g::<U>);
///    }
/// };
/// ```
///
/// `fn` also has a form with an explicit binder:
/// `for<T: Bound> fn A::<Vec<T>>::f => B::<T>::g`
/// uses the binder as the generic parameters of `_erasure`
/// instead of inferring them from the generic arguments of `#source`.
///
/// Wrapping the function in a `const _` avoids name clashes.
pub(crate) fn erase(tokens: TS1) -> TS1 {
    let decls =
        parse_macro_input!(tokens with Punctuated::<EraseDecl, Token![;]>::parse_terminated);
    let items = decls.iter().map(|decl| match decl {
        EraseDecl::Type { source, target, where_clause } => {
            let generics = erasure_generics(&source.qself, &source.path, where_clause);
            let (impl_generics, _, where_clause) = generics.split_for_impl();
            quote! {
                const _: () = {
                    #[creusot::no_translate]
                    #[creusot::spec::erasure_type]
                    fn _erasure #impl_generics (_: #source, _: #target) #where_clause {}
                };
            }
        }
        EraseDecl::Fn { binder, source, target, where_clause } => {
            let generics = match binder {
                Some(binder) => {
                    let mut generics = binder.clone();
                    if let Some(where_clause) = where_clause {
                        generics
                            .make_where_clause()
                            .predicates
                            .extend(where_clause.predicates.clone());
                    }
                    generics
                }
                None => erasure_generics(&source.qself, &source.path, where_clause),
            };
            let (impl_generics, _, where_clause) = generics.split_for_impl();
            quote! {
                const _: () = {
                    #[creusot::no_translate]
                    #[creusot::spec::erasure_fn]
                    fn _erasure #impl_generics () #where_clause {
                        let _ = (#source, #target);
                    }
                };
            }
        }
    });
    TS1::from(quote! { #(#items)* })
}
