use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Index,
};

pub fn derive_partial_eq(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let eq = partial_eq(&name, &input.data);

    let expanded = quote! {
        impl #impl_generics ::std::cmp::PartialEq for #name #ty_generics #where_clause {
            #[ensures(result == (self.deep_model() == rhs.deep_model()))]
            fn eq(&self, rhs: &Self) -> bool {
                #eq
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(std::cmp::PartialEq));
            type_param.bounds.push(parse_quote!(creusot_contracts::DeepModel));
        }
    }
    generics
}

fn partial_eq(base_ident: &Ident, data: &Data) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=>
                        self.#name.eq(&rhs.#name)
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
                        self.#index.eq(&rhs.#index)
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
                        let fields1 = arm.pattern_left;
                        let fields2 = arm.pattern_right;
                        let body = arm.body;
                        quote! { (#base_ident::#ident{#(#fields1),* }, #base_ident::#ident{#(#fields2),* }) => #body}
                    }
                    Fields::Unnamed(fields) => {
                        let arm = gen_match_arm(fields.unnamed.iter());
                        let fields1 = arm.pattern_left;
                        let fields2 = arm.pattern_right;
                        let body = arm.body;
                        quote! { (#base_ident::#ident(#(#fields1),*), #base_ident::#ident(#(#fields2),*)) => #body }
                    }
                    Fields::Unit => quote! {(#base_ident::#ident, #base_ident::#ident) => true},
                }
            });

            quote! {
                match (self, rhs) {
                    #(#arms),*,
                    _ => false
                }
            }
        }
        Data::Union(_) => todo!(),
    }
}

struct ArmAcc {
    pattern_left: Vec<TokenStream>,
    pattern_right: Vec<TokenStream>,
    body: TokenStream,
}

fn gen_match_arm<'a, I: Iterator<Item = &'a syn::Field>>(fields: I) -> ArmAcc {
    let mut acc =
        ArmAcc { pattern_left: Vec::new(), pattern_right: Vec::new(), body: quote!(true) };

    for (i, field) in fields.enumerate() {
        let named = field.ident.is_some();
        let name_base = match &field.ident {
            Some(ident) => format_ident!("{}", ident),
            None => format_ident!("v{}", i),
        };
        let name_1 = format_ident!("{}_1", name_base);
        let name_2 = format_ident!("{}_2", name_base);

        let cmp_expr = quote!(#name_1.eq(#name_2));

        let body = acc.body;
        acc.body = quote! { #cmp_expr && #body };
        if named {
            acc.pattern_left.push(quote!(#name_base: #name_1));
            acc.pattern_right.push(quote!(#name_base: #name_2));
        } else {
            acc.pattern_left.push(quote!(#name_1));
            acc.pattern_right.push(quote!(#name_2));
        }
    }

    acc
}
