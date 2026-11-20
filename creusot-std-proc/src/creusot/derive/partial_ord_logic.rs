use super::{
    deep_model::is_deep_model_ty,
    ord::discriminant_arms,
    visibility::{self, VisibilityExt},
};
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use syn::{
    Attribute, Data, DeriveInput, Fields, GenericParam, Generics, Visibility, parse_macro_input,
    parse_quote,
};

pub fn derive_partial_ord_logic(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let deep_model = is_deep_model_ty(&input.attrs);
    derive_partial_ord_logic_parsed(
        input.vis,
        input.ident,
        input.attrs,
        input.generics,
        input.data,
        deep_model,
    )
}

fn derive_partial_ord_logic_parsed(
    vis: Visibility,
    name: Ident,
    attrs: Vec<Attribute>,
    generics: Generics,
    data: Data,
    deep_model: bool,
) -> proc_macro::TokenStream {
    let generics = add_trait_bounds(generics, deep_model);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let lt_log = match partial_cmp_logic(&name, &data) {
        Ok(partial_cmp_logic) => partial_cmp_logic,
        Err(e) => return e.into_compile_error().into(),
    };

    let most_restrictive_vis = match data {
        Data::Struct(data) => {
            let is_non_exhaustive = attrs.iter().any(|attr| attr.path().is_ident("non_exhaustive"));
            visibility::struct_intersection(vis, is_non_exhaustive, &data)
        }
        _ => vis,
    };

    let open = most_restrictive_vis.format_openess();

    let expanded = quote! {
        impl #impl_generics ::creusot_std::logic::ord::PartialOrdLogic for #name #ty_generics #where_clause {
            #[::creusot_std::macros::logic(#open, inline)]
            fn lt_log(self, rhs: Self) -> bool {
                #lt_log
            }

            ::creusot_std::logic::ord::partial_ord_laws_impl! {}
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn add_trait_bounds(mut generics: Generics, deep_model: bool) -> Generics {
    let mut where_clause = generics.where_clause.take().unwrap_or_else(|| parse_quote!(where));

    for param in &mut generics.params {
        if let GenericParam::Type(type_param) = param {
            if deep_model {
                type_param.bounds.push(parse_quote!(::creusot_std::model::DeepModel));

                let ident = &type_param.ident;
                where_clause.predicates.push(parse_quote!(
                    <#ident as ::creusot_std::model::DeepModel>::DeepModelTy:
                        ::creusot_std::logic::ord::PartialOrdLogic
                ));
            } else {
                type_param.bounds.push(parse_quote!(::creusot_std::logic::ord::PartialOrdLogic));
            }
        }
    }

    generics.where_clause = Some(where_clause);
    generics
}

fn partial_cmp_logic(base_ident: &Ident, data: &Data) -> syn::Result<TokenStream> {
    match *data {
        Data::Struct(ref data) => {
            let acc = gen_match_arm(data.fields.iter());
            let pattern_left = acc.pattern_left;
            let pattern_right = acc.pattern_right;
            let body = acc.body;

            match &data.fields {
                Fields::Named(_) => Ok(quote! {
                    match (self, rhs) {
                        (Self { #(#pattern_left),* }, Self { #(#pattern_right),* }) => {
                            #body
                        }
                    }
                }),
                Fields::Unnamed(_) => Ok(quote! {
                    match (self, rhs) {
                        (Self(#(#pattern_left),*), Self(#(#pattern_right),*)) => {
                            #body
                        }
                    }
                }),
                Fields::Unit => Ok(quote! { false }),
            }
        }
        Data::Enum(ref data) => {
            if data.variants.is_empty() {
                let msg = "uninhabited types are currently unsupported";
                return Err(syn::Error::new(base_ident.span(), msg));
            }
            let discr_arms = discriminant_arms(&data.variants);
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let arm = gen_match_arm(fields.named.iter());
                        let fields1 = arm.pattern_left;
                        let fields2 = arm.pattern_right;
                        let body = arm.body;
                        quote! { (Self::#ident{#(#fields1),* }, Self::#ident{#(#fields2),* }) => {
                            #body
                        }}
                    }
                    Fields::Unnamed(fields) => {
                        let arm = gen_match_arm(fields.unnamed.iter());
                        let fields1 = arm.pattern_left;
                        let fields2 = arm.pattern_right;
                        let body = arm.body;
                        quote! { (Self::#ident(#(#fields1),*), Self::#ident(#(#fields2),*)) => {
                            #body
                        }}
                    }
                    Fields::Unit => quote! {(Self::#ident, Self::#ident) => false },
                }
            });

            Ok(quote! {
                let discriminant = |x: Self| match x { #discr_arms };
                match (self, rhs) {
                    #(#arms),*,
                    _ => ::creusot_std::logic::PartialOrdLogic::lt_log(discriminant.get(self), discriminant.get(rhs)),
                }
            })
        }
        Data::Union(_) => {
            Err(syn::Error::new(base_ident.span(), "cannot derive `PartialOrd` on a union"))
        }
    }
}

struct ArmAcc {
    pattern_left: Vec<TokenStream>,
    pattern_right: Vec<TokenStream>,
    body: TokenStream,
}

fn gen_match_arm<'a, I: Iterator<Item = &'a syn::Field>>(fields: I) -> ArmAcc {
    let mut pattern_left = Vec::new();
    let mut pattern_right = Vec::new();
    let mut bindings = Vec::new();

    for (i, field) in fields.enumerate() {
        let name_base = match &field.ident {
            Some(ident) => ident.clone(),
            None => format_ident!("v{}", i),
        };

        let name_1 = format_ident!("{}_1", name_base);
        let name_2 = format_ident!("{}_2", name_base);

        if field.ident.is_some() {
            pattern_left.push(quote!(#name_base: #name_1));
            pattern_right.push(quote!(#name_base: #name_2));
        } else {
            pattern_left.push(quote!(#name_1));
            pattern_right.push(quote!(#name_2));
        }

        bindings.push((name_1, name_2));
    }

    let mut bindings = bindings.into_iter().rev();

    let body = if let Some((first_1, first_2)) = bindings.next() {
        let acc = quote! {
            ::creusot_std::logic::ord::PartialOrdLogic::lt_log(
                #first_1, #first_2
            )
        };

        bindings.fold(acc, |acc, (name_1, name_2)| {
            quote! {
                ::creusot_std::logic::ord::PartialOrdLogic::lt_log(
                    #name_1, #name_2
                )
                ||
                (
                    #name_1 == #name_2
                    &&
                    (#acc)
                )
            }
        })
    } else {
        quote! { false }
    };

    ArmAcc { pattern_left, pattern_right, body }
}
