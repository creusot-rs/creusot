use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{
    Data, DeriveInput, Fields, GenericParam, Generics, Index, parse_macro_input, parse_quote,
    spanned::Spanned,
};

pub fn derive_clone(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let body = clone(&name, &input.data);
    let post = post(&name, &input.data);

    let expanded = quote! {
        impl #impl_generics ::std::clone::Clone for #name #ty_generics #where_clause {
            #[::creusot_contracts::ensures(#post)]
            fn clone(&self) -> Self {
                #body
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(::std::clone::Clone));
        }
    }
    generics
}

fn clone(base_ident: &Ident, data: &Data) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=> #name: ::std::clone::Clone::clone(&self.#name) }
                });
                quote! { #base_ident { #(#recurse),*} }
            }
            Fields::Unnamed(ref fields) => {
                let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span()=> ::std::clone::Clone::clone(&self.#index) }
                });
                quote! { #base_ident (#(#recurse),*) }
            }
            Fields::Unit => quote! { #base_ident },
        },
        Data::Enum(ref data) => {
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let ArmAcc {fields, body} = gen_match_arm(fields.named.iter());
                        quote! { #base_ident::#ident{#(#fields),* } => #base_ident::#ident{#(#body),* }}
                    }
                    Fields::Unnamed(fields) => {
                        let ArmAcc {fields, body} = gen_match_arm(fields.unnamed.iter());
                        quote! { #base_ident::#ident(#(#fields),*) => #base_ident::#ident(#(#body),* ) }
                    }
                    Fields::Unit => quote! {#base_ident::#ident => #base_ident::#ident},
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

#[derive(Default)]
struct ArmAcc {
    fields: Vec<TokenStream>,
    body: Vec<TokenStream>,
}

fn gen_match_arm<'a, I: Iterator<Item = &'a syn::Field>>(fields: I) -> ArmAcc {
    let mut acc: ArmAcc = Default::default();
    for (i, field) in fields.enumerate() {
        let named = field.ident.is_some();
        let name_base = match &field.ident {
            Some(ident) => format_ident!("{}", ident),
            None => format_ident!("v{}", i),
        };
        let name_1 = format_ident!("{}_1", name_base);

        let call = quote!(::std::clone::Clone::clone(&#name_1));
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

fn post(base_ident: &Ident, data: &Data) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let conjuncts = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    let ty = &f.ty;
                    quote_spanned! {f.span()=>
                        <#ty as ::std::clone::Clone>::clone.postcondition((&self.#name,), result.#name)
                    }
                });
                quote! { #(#conjuncts) && * }
            }
            Fields::Unnamed(ref fields) => {
                let conjuncts = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    let ty = &f.ty;
                    quote_spanned! {f.span()=>
                        <#ty as ::std::clone::Clone>::clone.postcondition((&self.#index,), result.#index)
                    }
                });
                quote! { #(#conjuncts) && * }
            }
            Fields::Unit => quote! { true },
        },
        Data::Enum(ref data) => {
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let ArmAccPost{ fields, fields_r, body } = gen_match_arm_post(fields.named.iter());
                        quote! {
                            (#base_ident::#ident{#(#fields),*}, #base_ident::#ident{#(#fields_r),*})  =>
                                #(#body) && *
                        }
                    }
                    Fields::Unnamed(fields) => {
                        let ArmAccPost{ fields, fields_r, body } = gen_match_arm_post(fields.unnamed.iter());
                        quote! {
                            (#base_ident::#ident(#(#fields),*), #base_ident::#ident(#(#fields_r),*)) =>
                                #(#body) && *
                        }
                    }
                    Fields::Unit => quote! { (#base_ident::#ident, #base_ident::#ident) => true },
                }
            });

            quote! {
                match (*self, result) {
                    #(#arms,)*
                    _ => false
                }
            }
        }
        Data::Union(_) => todo!(),
    }
}

#[derive(Default)]
struct ArmAccPost {
    fields: Vec<TokenStream>,
    fields_r: Vec<TokenStream>,
    body: Vec<TokenStream>,
}

fn gen_match_arm_post<'a, I: Iterator<Item = &'a syn::Field>>(fields: I) -> ArmAccPost {
    let mut acc: ArmAccPost = Default::default();
    for (i, field) in fields.enumerate() {
        let named = field.ident.is_some();
        let name_base = match &field.ident {
            Some(ident) => format_ident!("{}", ident),
            None => format_ident!("v{}", i),
        };
        let name_1 = format_ident!("{}_1", name_base);
        let name_r = format_ident!("{}_r", name_base);
        let ty = &field.ty;

        acc.body.push(quote!(
            <#ty as ::std::clone::Clone>::clone.postcondition((&#name_1,), #name_r)
        ));
        if named {
            acc.fields.push(quote!(#name_base: #name_1));
            acc.fields_r.push(quote!(#name_base: #name_r));
        } else {
            acc.fields.push(quote!(#name_1));
            acc.fields_r.push(quote!(#name_r));
        }
    }
    acc
}
