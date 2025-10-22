use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{
    Data, DeriveInput, Fields, GenericParam, Generics, Ident, parse_macro_input, parse_quote,
    spanned::Spanned,
};

/// Derive `Default` and `creusot_contracts::Default` on the given type.
pub fn derive_default(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let body_code = default_body(&input.data);
    let body_spec = default_spec(&input.data);

    quote! {
        impl #impl_generics ::std::default::Default for #name #ty_generics #where_clause {
            #[::creusot_contracts::macros::ensures(#body_spec)]
            fn default() -> Self {
                #body_code
            }
        }
    }
    .into()
}

/// Add `::std::defaut::Default` to these bounds.
fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(::std::default::Default));
        }
    }
    generics
}

/// The body of `default`.
fn default_body(data: &Data) -> TokenStream {
    match data {
        Data::Struct(data_struct) => {
            let fs = fields_set_to_default(&data_struct.fields);
            quote!( Self #fs )
        }
        Data::Enum(data_enum) => {
            let Some(default_variant) = data_enum
                .variants
                .iter()
                .find(|v| v.attrs.iter().any(|a| a.path().is_ident("default")))
            else {
                return syn::Error::new(Span::call_site(), "no default declared")
                    .into_compile_error();
            };

            let var_name = &default_variant.ident;
            let fs = fields_set_to_default(&default_variant.fields);

            quote!( Self :: #var_name #fs )
        }
        Data::Union(_) => {
            syn::Error::new(Span::call_site(), "this trait cannot be derived for unions")
                .into_compile_error()
        }
    }
}

/// Outputs `{ (f: FType::default(),)* }`, `((Type::default(),)*)` or an empty stream.
fn fields_set_to_default(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let fs = fields.named.iter().map(|f| {
                let name = &f.ident;
                quote_spanned! { f.span() => #name: ::std::default::Default::default() }
            });
            quote! { { #(#fs),* } }
        }
        Fields::Unnamed(fields) => {
            let fs = fields.unnamed.iter().map(|f| {
                quote_spanned! { f.span() => ::std::default::Default::default() }
            });
            quote! { ( #(#fs),* ) }
        }
        Fields::Unit => quote!({}),
    }
}

/// The body of the ensures clause.
fn default_spec(data: &Data) -> TokenStream {
    match data {
        Data::Struct(data_struct) => fields_are_default(&data_struct.fields, true),
        Data::Enum(data_enum) => {
            let Some(default_variant) = data_enum
                .variants
                .iter()
                .find(|v| v.attrs.iter().any(|a| a.path().is_ident("default")))
            else {
                return syn::Error::new(Span::call_site(), "no default declared")
                    .into_compile_error();
            };

            let var_name = &default_variant.ident;

            let pat = match &default_variant.fields {
                Fields::Named(fields) => {
                    let fs = fields.named.iter().map(|f| {
                        let name = &f.ident;
                        quote_spanned! { f.span() => #name }
                    });
                    quote!( { #(#fs),* } )
                }
                Fields::Unnamed(fields) => {
                    let fs = fields.unnamed.iter().enumerate().map(|(i, f)| {
                        let name = Ident::new(&format!("x{i}"), f.span());
                        quote_spanned! { f.span() => #name }
                    });
                    quote!( ( #(#fs),* ) )
                }
                Fields::Unit => quote!(),
            };

            let expr = fields_are_default(&default_variant.fields, false);

            quote!( match result { Self :: #var_name #pat => #expr , _ => false } )
        }
        Data::Union(_) => {
            syn::Error::new(Span::call_site(), "this trait cannot be derived for unions")
                .into_compile_error()
        }
    }
}

/// If `with_result` is `true`, we are accessing `result`.
///
/// Else, this is a struct in an enum case. In the case of a tuple struct, assume that the
/// variables are named `x1 ... xn`.
fn fields_are_default(fields: &Fields, with_result: bool) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let fs = fields.named.iter().map(|f| {
                let name = &f.ident;
                if with_result {
                    quote_spanned! { f.span() => creusot_contracts::std::ops::FnExt::postcondition(::std::default::Default::default, (), result.#name) }
                } else {
                    quote_spanned! { f.span() => creusot_contracts::std::ops::FnExt::postcondition(::std::default::Default::default, (), #name) }
                }
            });
            quote! { true #(&& #fs)* }
        }
        Fields::Unnamed(fields) => {
            let fs = fields.unnamed.iter().enumerate().map(|(i, f)| {
                if with_result {
                    let i = syn::LitInt::new(&format!("{i}"), f.span());
                    quote_spanned! { f.span() => creusot_contracts::std::ops::FnExt::postcondition(::std::default::Default::default, (), result.#i) }
                } else {
                    let name = Ident::new(&format!("x{i}"), f.span());
                    quote_spanned! { f.span() => creusot_contracts::std::ops::FnExt::postcondition(::std::default::Default::default, (), #name) }
                }
            });
            quote! { true #(&& #fs)* }
        }
        Fields::Unit => quote!(true),
    }
}
