use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Ident,
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
            #[::creusot_contracts::ensures(result.is_default())]
            fn default() -> Self {
                #body_code
            }
        }

        impl #impl_generics ::creusot_contracts::std::default::Default for #name #ty_generics #where_clause {
            #[::creusot_contracts::predicate(prophetic)]
            #[::creusot_contracts::open]
            fn is_default(self) -> bool {
                use ::creusot_contracts::std::default::Default as _;
                #body_spec
            }
        }
    }
    .into()
}

/// Add `creusot_contracts::Default` to these bounds.
fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(::creusot_contracts::std::default::Default));
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
                let ty = &f.ty;
                quote_spanned! { f.span() => #name : <#ty>::default() }
            });
            quote! { { #(#fs),* } }
        }
        Fields::Unnamed(fields) => {
            let fs = fields.unnamed.iter().map(|f| {
                let ty = &f.ty;
                quote_spanned! { f.span() => <#ty>::default() }
            });
            quote! { ( #(#fs),* ) }
        }
        Fields::Unit => quote!({}),
    }
}

/// The body of `is_default`.
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

            quote!( match self { Self :: #var_name #pat => #expr , _ => false } )
        }
        Data::Union(_) => {
            syn::Error::new(Span::call_site(), "this trait cannot be derived for unions")
                .into_compile_error()
        }
    }
}

/// If `with_self` is `true`, we are accessing `self`.
///
/// Else, this is a struct in an enum case. In the case of a tuple struct, assume that the
/// variables are named `x1 ... xn`.
fn fields_are_default(fields: &Fields, with_self: bool) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let fs = fields.named.iter().map(|f| {
                let name = &f.ident;
                if with_self {
                    quote_spanned! { f.span() => self.#name.is_default() }
                } else {
                    quote_spanned! { f.span() => #name.is_default() }
                }
            });
            quote! { true #(&& #fs)* }
        }
        Fields::Unnamed(fields) => {
            let fs = fields.unnamed.iter().enumerate().map(|(i, f)| {
                if with_self {
                    let i = syn::LitInt::new(&format!("{i}"), f.span());
                    quote_spanned! { f.span() => self.#i.is_default() }
                } else {
                    let name = Ident::new(&format!("x{i}"), f.span());
                    quote_spanned! { f.span() => #name.is_default() }
                }
            });
            quote! { true #(&& #fs)* }
        }
        Fields::Unit => quote!(true),
    }
}
