use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{Data, DeriveInput, Fields, Index, parse_macro_input, spanned::Spanned};

pub fn derive_resolve(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let eq = match resolve(&name, &input.data) {
        Ok(eq) => eq,
        Err(e) => return e.into_compile_error().into(),
    };

    let expanded = quote! {
        impl #impl_generics ::creusot_contracts::Resolve for #name #ty_generics #where_clause {
            #[::creusot_contracts::logic(open, prophetic)]
            fn resolve(self) -> bool {
                #eq
            }

            #[::creusot_contracts::logic(open(self), prophetic)]
            #[::creusot_contracts::requires(::creusot_contracts::resolve::structural_resolve(self))]
            #[::creusot_contracts::ensures(self.resolve())]
            fn resolve_coherence(self) {}
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn resolve(base_ident: &Ident, data: &Data) -> syn::Result<TokenStream> {
    match *data {
        Data::Struct(ref data) => Ok(match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=>
                        ::creusot_contracts::resolve(self.#name)
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
                        ::creusot_contracts::resolve(self.#index)
                    }
                });
                quote! {
                    #(#recurse)&&*
                }
            }
            Fields::Unit => quote! {
                true
            },
        }),
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

            Ok(quote! {
                match self {
                    #(#arms),*
                }
            })
        }
        Data::Union(_) => {
            Err(syn::Error::new(base_ident.span(), "cannot derive `Resolve` on a union"))
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

        let call = quote!(::creusot_contracts::resolve(#name_1));
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
