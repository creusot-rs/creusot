use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Index,
};

pub fn derive_invariant(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let inv = invariant(&name, &input.data);

    let expanded = quote! {
        impl #impl_generics ::creusot_contracts::invariant::Invariant for #name #ty_generics #where_clause {
            #[predicate]
            fn invariant(self) -> bool {
                #inv
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(::std::cmp::PartialEq));
            type_param.bounds.push(parse_quote!(::creusot_contracts::model::DeepModel));
        }
    }
    generics
}

fn invariant(base_ident: &Ident, data: &Data) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=>
                        self.#name.invariant()
                    }
                });
                quote! {
                    #(#recurse)&&*
                }
            }
            Fields::Unnamed(ref fields) => {
                let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span()=>
                        self.#index.invariant()
                    }
                });
                quote! {
                    #(#recurse)&&*
                }
            }
            Fields::Unit => {
                quote!(true)
            }
        },
        Data::Enum(ref data) => {
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let arm = gen_match_arm(fields.named.iter());
                        let pattern = arm.pattern;
                        let body = arm.body;
                        quote! { #base_ident::#ident{#(#pattern),* } => #body}
                    }
                    Fields::Unnamed(fields) => {
                        let arm = gen_match_arm(fields.unnamed.iter());
                        let pattern = arm.pattern;
                        let body = arm.body;
                        quote! { #base_ident::#ident(#(#pattern),*) => #body }
                    }
                    Fields::Unit => quote! {#base_ident::#ident => true},
                }
            });

            quote! {
                match self {
                    #(#arms),*,
                    _ => false
                }
            }
        }
        Data::Union(_) => todo!(),
    }
}

struct ArmAcc {
    pattern: Vec<TokenStream>,
    body: TokenStream,
}

fn gen_match_arm<'a, I: Iterator<Item = &'a syn::Field>>(fields: I) -> ArmAcc {
    let mut acc = ArmAcc { pattern: Vec::new(), body: quote!(true) };

    for (i, field) in fields.enumerate() {
        let name = match &field.ident {
            Some(ident) => format_ident!("{}", ident),
            None => format_ident!("v{}", i),
        };

        let inv_expr = quote!(#name.invariant());
        let body = acc.body;
        acc.body = quote! { #inv_expr && #body };

        acc.pattern.push(quote!(#name));
    }

    acc
}
