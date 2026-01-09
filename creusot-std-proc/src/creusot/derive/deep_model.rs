use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{
    Data, DeriveInput, Error, Expr, ExprLit, Fields, GenericParam, Generics, Index, Lit, Meta,
    MetaNameValue, Path, parse_macro_input, parse_quote, spanned::Spanned,
};

pub fn derive_deep_model(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let vis = input.vis;

    let (deep_model_ty_name, ty) = if let Some(attr) =
        input.attrs.into_iter().find(|p| p.path().is_ident("DeepModelTy"))
    {
        let name = match parse_deep_model_ty_attr(attr.meta) {
            Err(e) => return e.to_compile_error().into(),
            Ok(o) => o,
        };

        (name, None)
    } else {
        let ident = Ident::new(&format!("{}DeepModel", name), proc_macro::Span::def_site().into());
        let deep_model_ty = match deep_model_ty(&ident, &generics, &input.data) {
            Ok(t) => t,
            Err(e) => return e.to_compile_error().into(),
        };

        (ident.into(), Some(quote! { #vis #deep_model_ty }))
    };

    let eq = match deep_model(&name, &deep_model_ty_name, &input.data) {
        Ok(eq) => eq,
        Err(e) => return e.into_compile_error().into(),
    };

    let open = match vis {
        syn::Visibility::Public(_) => quote!(open),
        syn::Visibility::Restricted(res) => quote!(open(#res)),
        syn::Visibility::Inherited => quote!(open(self)),
    };

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

fn parse_deep_model_ty_attr(m: Meta) -> syn::Result<Path> {
    match m {
        Meta::NameValue(MetaNameValue {
            value: Expr::Lit(ExprLit { lit: Lit::Str(l), .. }),
            ..
        }) => {
            let token = l.value();
            Ok(syn::parse_str(&token)?)
        }
        _ => Err(Error::new(m.span(), "Expected `=` followed by type name")),
    }
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

                quote! { #ident #fields }
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
