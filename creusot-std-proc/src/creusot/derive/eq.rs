use syn::{
    Data, DeriveInput, GenericParam, Generics, Type, parse_macro_input, parse_quote,
    spanned::Spanned,
};

pub fn derive_eq(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;
    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let assertions = match eq_assertions(&input.data) {
        Ok(assertions) => assertions,
        Err(e) => return e.into_compile_error().into(),
    };

    quote::quote! {
        impl #impl_generics ::core::cmp::Eq for #name #ty_generics #where_clause {}
        const _: () = {
            trait AssertEq {
                fn assert_receiver_is_total_eq(&self);
            }

            impl #impl_generics AssertEq for #name #ty_generics #where_clause {
                fn assert_receiver_is_total_eq(&self) {
                    fn assert_eq<T: ::core::cmp::Eq>() {}
                    #(assert_eq::<#assertions>();)*
                }
            }
        };
    }
    .into()
}

fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(type_param) = param {
            type_param.bounds.push(parse_quote!(::core::cmp::Eq));
            type_param.bounds.push(parse_quote!(::creusot_std::model::DeepModel));
        }
    }
    generics
}

fn eq_assertions(data: &Data) -> syn::Result<Vec<&Type>> {
    match data {
        Data::Struct(data) => {
            let result = data.fields.iter().map(|field| &field.ty).collect::<Vec<_>>();
            Ok(result)
        }
        Data::Enum(data) => {
            let result = data
                .variants
                .iter()
                .flat_map(|variant| variant.fields.iter().map(|field| &field.ty))
                .collect::<Vec<_>>();
            Ok(result)
        }
        Data::Union(data) => {
            Err(syn::Error::new(data.union_token.span(), "cannot derive `Eq` on a union"))
        }
    }
}
