use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Index,
};

pub fn derive_deep_model(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let deep_model_ty_name =
        Ident::new(&format!("{}DeepModel", name.to_string()), proc_macro::Span::def_site().into());
    let deep_model_ty = deep_model_ty(&deep_model_ty_name, &input.data);
    let eq = deep_model(&name, &deep_model_ty_name, &input.data);

    let expanded = quote! {
        #deep_model_ty

        impl #impl_generics ::creusot_contracts::DeepModel for #name #ty_generics #where_clause {
            type DeepModelTy = #deep_model_ty_name;

            #[logic]
            fn deep_model(self) -> Self::DeepModelTy {
                #eq
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(::creusot_contracts::DeepModel));
            // type_param.bounds.push(parse_quote!(::creusot_contracts::model::DeepModel));
        }
    }
    generics
}

fn deep_model_ty_fields(base_ident: &Ident, fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(ref fields) => {
            let recurse = fields.named.iter().map(|f| {
                let name = &f.ident;
                let ty = &f.ty;
                quote_spanned! {f.span()=>
                    #name: < #ty as creusot_contracts::DeepModel> :: DeepModelTy
                }
            });
            quote! {
                #base_ident { #(#recurse),*}
            }
        }
        Fields::Unnamed(ref fields) => {
            let recurse = fields.unnamed.iter().enumerate().map(|(_, f)| {
                let ty = &f.ty;
                quote_spanned! {f.span()=>
                    #ty :: DeepModelTy
                }
            });
            quote! {
                #base_ident (#(#recurse),*)
            }
        }
        Fields::Unit => quote! {
            #base_ident
        },
    }
}

fn deep_model_ty(base_ident: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(ref data) => {
            let data = deep_model_ty_fields(base_ident, &data.fields);
            quote! { struct  #data }
        }
        Data::Enum(ref data) => {
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                deep_model_ty_fields(ident, &v.fields)
            });

            quote! {
                enum #base_ident {
                    #(#arms),*
                }
            }
        }
        Data::Union(_) => todo!(),
    }
}

fn deep_model(src_ident: &Ident, tgt_ident: &Ident, data: &Data) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=>
                        #name: self.#name.deep_model()
                    }
                });
                quote! {
                    #tgt_ident { #(#recurse),*}
                }
            }
            Fields::Unnamed(ref fields) => {
                let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span()=>
                        self.#index.deep_model()
                    }
                });
                quote! {
                    #tgt_ident (#(#recurse),*)
                }
            }
            Fields::Unit => quote! {
                #tgt_ident
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
