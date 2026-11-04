use super::visibility::{self, VisibilityExt};
use proc_macro::{Diagnostic, Level};
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{
    Attribute, Data, DeriveInput, Error, Expr, ExprLit, Fields, GenericParam, Generics, Index, Lit,
    Meta, MetaNameValue, Path, Token, parse_macro_input, parse_quote, punctuated::Punctuated,
    spanned::Spanned,
};

pub fn derive_deep_model(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let non_exhaustive_attr =
        input.attrs.iter().find(|attr| attr.path().is_ident("non_exhaustive")).cloned();

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let vis = input.vis;

    let mut first_ty_name_attr = None;
    let mut repeated_ty_name_attr_spans = Vec::new();
    let mut derives = Vec::new();
    for attr in input.attrs.into_iter() {
        if attr.path().is_ident("DeepModelTy") {
            match (parse_deep_model_ty_attr(&attr.meta), &first_ty_name_attr) {
                (Err(e), _) => return e.to_compile_error().into(),
                (Ok(DeepModelTyAttr::Path(path)), None) => {
                    first_ty_name_attr = Some((path, attr.span().unwrap()))
                }
                (Ok(DeepModelTyAttr::Path(_)), Some(_)) => {
                    repeated_ty_name_attr_spans.push(attr.span().unwrap())
                }
                (Ok(DeepModelTyAttr::Derives(append)), _) => {
                    derives.push((append, attr.span().unwrap()))
                }
            };
        }
    }
    let (deep_model_ty_name, ty) = if let Some((name, span)) = first_ty_name_attr {
        if !repeated_ty_name_attr_spans.is_empty() {
            Diagnostic::new(Level::Error, "name of `DeepModelTy` specified multiple times")
                .span_note(span, "previous definition of the type name here")
                .span_error(
                    &*repeated_ty_name_attr_spans,
                    "name of `DeepModelTy` specified again here",
                )
                .span_help(repeated_ty_name_attr_spans, "delete the repeated attributes")
                .note("the name of `DeepModelTy` must be specified at most once")
                .emit();
        }
        if !derives.is_empty() {
            let diag = Diagnostic::new(Level::Error, "cannot put derives on external type");
            let mut derive_spans = derives.iter().map(|(_, span)| *span).peekable();

            let before = std::iter::from_fn(|| {
                derive_spans.next_if(|s| s.byte_range().start < span.byte_range().start)
            })
            .collect::<Vec<_>>();

            let after = derive_spans.collect::<Vec<_>>();
            let diag = if before.is_empty() {
                diag.span_note(span, "use of external type requested here")
                    .span_error(after, "derives specified here")
            } else {
                let diag = diag
                    .span_note(before, "derives specified here")
                    .span_error(span, "use of external type requested here");
                if after.is_empty() {
                    diag
                } else {
                    diag.span_note(after, "additional derives specified here")
                }
            };
            diag.emit()
        }

        (name, None)
    } else {
        let ident = Ident::new(&format!("{}DeepModel", name), proc_macro::Span::def_site().into());
        let deep_model_ty = match deep_model_ty(&ident, &generics, &input.data) {
            Ok(t) => t,
            Err(e) => return e.to_compile_error().into(),
        };

        // inform all derives that this is a deep model type
        let deep_model_ty_atrr = (!derives.is_empty()).then_some(quote!(#[DeepModelTy]));
        let derives = derives.iter().map(|(derive, _)| derive);
        (
            ident.into(),
            Some(
                quote! { #(#[derive(#derives)])* #deep_model_ty_atrr #non_exhaustive_attr #vis #deep_model_ty },
            ),
        )
    };

    let eq = match deep_model(&name, &deep_model_ty_name, &input.data) {
        Ok(eq) => eq,
        Err(e) => return e.into_compile_error().into(),
    };

    let most_restrictive_vis_so_far = vis.clone();
    let most_restrictive_vis = match input.data {
        Data::Struct(data) => {
            visibility::struct_intersection(vis.clone(), non_exhaustive_attr.is_some(), &data)
        }
        _ => most_restrictive_vis_so_far,
    };

    let open = most_restrictive_vis.format_openess();

    let expanded = quote! {
        #ty

        impl #impl_generics ::creusot_std::model::DeepModel for #name #ty_generics #where_clause {
            type DeepModelTy = #deep_model_ty_name #ty_generics;

            #[::creusot_std::macros::logic(#open)]
            fn deep_model(self) -> <Self as ::creusot_std::model::DeepModel>::DeepModelTy {
                #eq
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

/// Checks if the type this is being derived for is a `DeepModelTy`
pub(crate) fn is_deep_model_ty(attrs: &[Attribute]) -> bool {
    let mut deep_model_attr = None;
    let mut repeated_deep_model_attrs = Vec::new();

    for attr in attrs.into_iter() {
        if attr.path().is_ident("DeepModelTy") {
            match attr.meta {
                Meta::Path(_) => match deep_model_attr {
                    Some(_) => repeated_deep_model_attrs.push(attr.span().unwrap()),
                    None => deep_model_attr = Some(attr.span().unwrap()),
                },
                Meta::NameValue(_) | Meta::List(_) => (),
            }
        }
    }
    if let Some(span) = deep_model_attr {
        if !repeated_deep_model_attrs.is_empty() {
            Diagnostic::new(Level::Error, "`DeepModelTy` specified multiple times")
                .span_note(span, "previous `DeepModelTy` attributes")
                .span_error(&*repeated_deep_model_attrs, "`DeepModelTy` specified again here")
                .span_help(repeated_deep_model_attrs, "delete the repeated attributes")
                .note("`DeepModelTy` must be specified at most once")
                .emit();
        }
        true
    } else {
        false
    }
}

// FIXME: `TypePath` should be used instead of `Path` however it causes problems when constructing
// the type because of unstable feature https://github.com/rust-lang/rust/issues/86935. The
// stabilization seems to be just around the corner, so this can be changed afterwards.
fn parse_deep_model_ty_attr(m: &Meta) -> syn::Result<DeepModelTyAttr> {
    match m {
        Meta::NameValue(MetaNameValue {
            value: Expr::Lit(ExprLit { lit: Lit::Str(l), .. }),
            ..
        }) => {
            let token = l.value();
            Ok(DeepModelTyAttr::Path(syn::parse_str(&token)?))
        }
        Meta::List(list) => {
            use syn::{Error, Meta, Path, Token, punctuated::Punctuated};

            let nested: Meta = list.parse_args()?;

            let derives = match nested {
                Meta::List(list) if list.path.is_ident("derive") => {
                    list.parse_args_with(Punctuated::<Path, Token![,]>::parse_terminated)?
                }
                other => {
                    return Err(Error::new_spanned(other, "only derive(...) is currently allowed"));
                }
            };

            warn_unneeded_deep_model_ty_derives(&derives);

            Ok(DeepModelTyAttr::Derives(derives))
        }
        Meta::NameValue(MetaNameValue { value, .. }) => {
            Err(Error::new(value.span(), "expected a literal"))
        }
        Meta::Path(_) => {
            let msg = "`DeepModelTy` without value attribute means that this already is a deep model of a type and you shouldn't need to derive `DeepModel` on such type";
            Err(Error::new(m.span(), msg))
        }
    }
}

enum DeepModelTyAttr {
    Path(Path),
    Derives(Punctuated<Path, Token![,]>),
}

fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(::creusot_std::model::DeepModel));
        }
    }
    generics
}

fn deep_model_ty_fields(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let recurse = fields.named.iter().map(|f| {
                let name = &f.ident;
                let ty = &f.ty;
                let vis = &f.vis;
                quote_spanned! {f.span()=>
                    #vis #name: < #ty as ::creusot_std::model::DeepModel> :: DeepModelTy
                }
            });
            quote! {
                 { #(#recurse),*}
            }
        }
        Fields::Unnamed(fields) => {
            let recurse = fields.unnamed.iter().map(|f| {
                let ty = &f.ty;
                let vis = &f.vis;
                quote_spanned! {f.span()=>
                   #vis < #ty as ::creusot_std::model::DeepModel> :: DeepModelTy
                }
            });
            quote! {
                 (#(#recurse),*)
            }
        }
        Fields::Unit => quote! {},
    }
}

fn deep_model_ty(base_ident: &Ident, generics: &Generics, data: &Data) -> syn::Result<TokenStream> {
    match data {
        Data::Struct(data) => {
            let semi_colon = data.semi_token;
            let data = deep_model_ty_fields(&data.fields);
            Ok(quote! { struct #base_ident #generics #data #semi_colon })
        }
        Data::Enum(data) => {
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                let fields = deep_model_ty_fields(&v.fields);
                match &v.discriminant {
                    Some((token, val)) => quote! { #ident #fields #token #val },
                    None => quote! { #ident #fields },
                }
            });

            Ok(quote! {
                enum #base_ident #generics {
                    #(#arms),*
                }
            })
        }
        Data::Union(_) => {
            Err(syn::Error::new(base_ident.span(), "cannot derive `DeepModel` on a union"))
        }
    }
}

fn deep_model(src_ident: &Ident, tgt_ident: &Path, data: &Data) -> syn::Result<TokenStream> {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=>
                        #name: ::creusot_std::model::DeepModel::deep_model(self.#name)
                    }
                });
                Ok(quote! {
                    #tgt_ident { #(#recurse),*}
                })
            }
            Fields::Unnamed(ref fields) => {
                let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span()=>
                        ::creusot_std::model::DeepModel::deep_model(self.#index)
                    }
                });
                Ok(quote! {
                    #tgt_ident (#(#recurse),*)
                })
            }
            Fields::Unit => Ok(quote! {
                #tgt_ident
            }),
        },
        Data::Enum(ref data) => {
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let arm = gen_match_arm(fields.named.iter());
                        let fields1 = arm.fields;
                        let body = arm.body;
                        quote! { #src_ident::#ident{#(#fields1),* } => #tgt_ident::#ident{#(#body),* }}
                    }
                    Fields::Unnamed(fields) => {
                        let arm = gen_match_arm(fields.unnamed.iter());
                        let fields1 = arm.fields;
                        let body = arm.body;
                        quote! { #src_ident::#ident(#(#fields1),*) => #tgt_ident::#ident(#(#body),* ) }
                    }
                    Fields::Unit => quote! {#src_ident::#ident => #tgt_ident::#ident},
                }
            });

            Ok(quote! {
                match self {
                    #(#arms),*
                }
            })
        }
        Data::Union(_) => {
            Err(syn::Error::new(src_ident.span(), "cannot derive `DeepModel` on a union"))
        }
    }
}

struct ArmAcc {
    fields: Vec<TokenStream>,
    body: Vec<TokenStream>,
}

fn gen_match_arm<'a, I: Iterator<Item = &'a syn::Field>>(fields: I) -> ArmAcc {
    let mut acc = ArmAcc { fields: Vec::new(), body: Vec::new() };

    for (i, field) in fields.enumerate() {
        let named = field.ident.is_some();
        let name_base = match &field.ident {
            Some(ident) => format_ident!("{}", ident),
            None => format_ident!("v{}", i),
        };
        let name_1 = format_ident!("{}_1", name_base);

        let call = quote!(#name_1.deep_model());
        if named {
            acc.fields.push(quote!(#name_base: #name_1));
            acc.body.push(quote!(#name_base: #call));
        } else {
            acc.fields.push(quote!(#name_1));
            acc.body.push(quote!(#call));
        }
    }

    acc
}

fn warn_unneeded_deep_model_ty_derives<'a>(derives: impl IntoIterator<Item = &'a Path>) {
    // Implementing these on `DeepModelTy` is useless, so warn about them
    // We also add `Serialize` and `Deserialize` because of popularity of serde.
    // If other people want to create a logic derive for creusot they can just name their derives
    // differently. E.g. `SerializeLogic`.
    const UNNEEDED_DERIVES: &[&str] = &[
        "Clone",
        "Copy",
        "Debug",
        "Default",
        "Deserialize",
        "Eq",
        "Hash",
        "Ord",
        "PartialEq",
        "PartialOrd",
        "Serialize",
    ];

    for path in derives {
        if path.segments.last().is_some_and(|segment| {
            // This is imperfect because people can rename derives but I don't expect anyone to do
            // that. Maybe it's even desirable given diagnostic don't support named lint levels, so
            // in the unlikely case this is FP people can rename the derive to silence the warning.
            UNNEEDED_DERIVES.iter().any(|&name| segment.ident == name)
        }) {
            Diagnostic::spanned(
                path.span().unwrap(),
                Level::Warning,
                "this derive shouldn't be needed for the DeepModel's type",
            )
            .emit();
        }
    }
}
