use super::deep_model::is_deep_model_ty;
use proc_macro2::{Ident, TokenStream};
use quote::quote;
use syn::{Data, DeriveInput, Field, GenericParam, Generics, parse_macro_input, parse_quote};

pub fn derive_ord_logic(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    derive_ord_logic_parsed(input.ident, input.generics, input.data, is_deep_model_ty(&input.attrs))
}

pub fn derive_ord_logic_parsed(
    name: Ident,
    generics: Generics,
    data: Data,
    deep_model: bool,
) -> proc_macro::TokenStream {
    let generics = add_trait_bounds(generics, deep_model);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    fn instantiate_law(fields: &syn::Fields) -> impl Iterator<Item = TokenStream> {
        fields.iter().map(|Field { ty, .. }| {
            quote! {
                let _ = <#ty as ::creusot_std::logic::ord::OrdLogic>::lt_log_total;
            }
        })
    }

    let laws = match data {
        Data::Struct(data) => instantiate_law(&data.fields).collect::<Vec<_>>(),
        Data::Enum(data) => {
            if data.variants.is_empty() {
                return syn::Error::new(name.span(), "uninhabited types are currently unsupported")
                    .into_compile_error()
                    .into();
            }
            data.variants.iter().flat_map(|variant| instantiate_law(&variant.fields)).collect()
        }
        Data::Union(_) => {
            return syn::Error::new(name.span(), "cannot derive `Ord` on a union")
                .into_compile_error()
                .into();
        }
    };

    let expanded = quote! {
        impl #impl_generics ::creusot_std::logic::ord::OrdLogic for #name #ty_generics #where_clause {
            #[::creusot_std::macros::logic(law)]
            #[::creusot_std::macros::ensures(self < other || self == other || other < self)]
            fn lt_log_total(self, other: Self) {
                #(#laws)*
            }
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
                        ::creusot_std::logic::ord::OrdLogic
                ));
            } else {
                type_param.bounds.push(parse_quote!(::creusot_std::logic::ord::OrdLogic));
            }
        }
    }

    generics.where_clause = Some(where_clause);
    generics
}
