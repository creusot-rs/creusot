use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{parse_macro_input, spanned::Spanned, Data, DeriveInput, Fields, Index};

pub fn derive_resolve(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let eq = resolve(&name, &input.data);

    let expanded = quote! {
        #[::creusot_contracts::trusted]
        impl #impl_generics ::creusot_contracts::Resolve for #name #ty_generics #where_clause {
            #[predicate]
            #[open]
            fn resolve(self) -> bool {
                use ::creusot_contracts::Resolve;
                #eq
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn resolve(base_ident: &Ident, data: &Data) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=>
                        Resolve::resolve(&self.#name)
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
                        Resolve::resolve(&self.#index)
                    }
                });
                quote! {
                    #(#recurse)&&*
                }
            }
            Fields::Unit => quote! {
                true
            },
        },
        Data::Enum(ref data) => {
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let arm = gen_match_arm(fields.named.iter());
                        let fields1 = arm.fields;
                        let body = arm.body;
                        quote! { #base_ident::#ident{#(#fields1),* } => #(#body)&&* }
                    }
                    Fields::Unnamed(fields) => {
                        let arm = gen_match_arm(fields.unnamed.iter());
                        let fields1 = arm.fields;
                        let body = arm.body;
                        quote! { #base_ident::#ident(#(#fields1),*) => #(#body)&&* }
                    }
                    Fields::Unit => quote! {#base_ident::#ident =>  true },
                }
            });

            quote! {
                match self {
                    #(#arms),*
                }
            }
        }
        Data::Union(_) => todo!(),
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

        let call = quote!(Resolve::resolve(&#name_1));
        if named {
            acc.fields.push(quote!(#name_base: #name_1));
            acc.body.push(quote!(#call));
        } else {
            acc.fields.push(quote!(#name_1));
            acc.body.push(quote!(#call));
        }
    }

    acc
}
