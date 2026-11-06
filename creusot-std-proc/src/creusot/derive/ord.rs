use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{
    Data, DeriveInput, Expr, ExprLit, Fields, GenericParam, Generics, Index, Lit, LitInt, Token,
    Variant, parse_macro_input, parse_quote, punctuated::Punctuated, spanned::Spanned,
};

pub fn derive_ord(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let cmp = match cmp(&name, &input.data) {
        Ok(cmp) => cmp,
        Err(e) => return e.into_compile_error().into(),
    };

    let expanded = quote! {
        impl #impl_generics ::core::cmp::Ord for #name #ty_generics #where_clause {
            #[::creusot_std::macros::ensures(result == (::creusot_std::logic::ord::OrdLogic::cmp_log(::creusot_std::model::DeepModel::deep_model(self), ::creusot_std::model::DeepModel::deep_model(rhs))))]
            fn cmp(&self, rhs: &Self) -> ::core::cmp::Ordering {
                #cmp
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn add_trait_bounds(mut generics: Generics) -> Generics {
    let mut where_clause = generics.where_clause.take().unwrap_or_else(|| parse_quote!(where));

    for param in &mut generics.params {
        if let GenericParam::Type(type_param) = param {
            type_param.bounds.push(parse_quote!(::core::cmp::Ord));
            type_param.bounds.push(parse_quote!(::creusot_std::model::DeepModel));

            let ident = &type_param.ident;
            where_clause.predicates.push(parse_quote!(
                <#ident as ::creusot_std::model::DeepModel>::DeepModelTy:
                    ::creusot_std::logic::ord::OrdLogic
            ));
        }
    }

    generics.where_clause = Some(where_clause);
    generics
}

fn cmp(base_ident: &Ident, data: &Data) -> syn::Result<TokenStream> {
    match *data {
        Data::Struct(ref data) => Ok(match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span()=>
                       let ord = ::core::cmp::Ord::cmp(&self.#name, &rhs.#name);
                       if ord.is_ne() { return ord }
                    }
                });
                quote! {
                    #(#recurse)*
                    ::core::cmp::Ordering::Equal
                }
            }
            Fields::Unnamed(ref fields) => {
                let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span()=>
                        let ord = ::core::cmp::Ord::cmp(&self.#index, &rhs.#index);
                        if ord.is_ne() { return ord }
                    }
                });
                quote! {
                    #(#recurse)*
                    ::core::cmp::Ordering::Equal
                }
            }
            Fields::Unit => {
                quote! { ::core::cmp::Ordering::Equal }
            }
        }),
        Data::Enum(ref data) => {
            if data.variants.is_empty() {
                return Ok(quote! { match *self {} });
            }
            let discr_arms = discriminant_arms(&data.variants);
            let arms = data.variants.iter().map(|v| {
                let ident = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let arm = gen_match_arm(fields.named.iter());
                        let fields1 = arm.pattern_left;
                        let fields2 = arm.pattern_right;
                        let body = arm.body;
                        quote! { (#base_ident::#ident{#(#fields1),* }, #base_ident::#ident{#(#fields2),* }) => {
                            #body
                            ::core::cmp::Ordering::Equal
                        }}
                    }
                    Fields::Unnamed(fields) => {
                        let arm = gen_match_arm(fields.unnamed.iter());
                        let fields1 = arm.pattern_left;
                        let fields2 = arm.pattern_right;
                        let body = arm.body;
                        quote! { (#base_ident::#ident(#(#fields1),*), #base_ident::#ident(#(#fields2),*)) => {
                            #body
                            ::core::cmp::Ordering::Equal
                        }}
                    }
                    Fields::Unit => quote! {(#base_ident::#ident, #base_ident::#ident) => ::core::cmp::Ordering::Equal },
                }
            });

            Ok(quote! {
                let discriminant = |x: &Self| match x { #discr_arms };
                match (self, rhs) {
                    #(#arms),*,
                    _ => discriminant(self).cmp(&discriminant(rhs)),
                }
            })
        }
        Data::Union(_) => Err(syn::Error::new(base_ident.span(), "cannot derive `Ord` on a union")),
    }
}

struct ArmAcc {
    pattern_left: Vec<TokenStream>,
    pattern_right: Vec<TokenStream>,
    body: TokenStream,
}

fn gen_match_arm<'a, I: Iterator<Item = &'a syn::Field>>(fields: I) -> ArmAcc {
    let mut acc =
        ArmAcc { pattern_left: Vec::new(), pattern_right: Vec::new(), body: TokenStream::new() };

    for (i, field) in fields.enumerate() {
        let named = field.ident.is_some();
        let name_base = match &field.ident {
            Some(ident) => format_ident!("{}", ident),
            None => format_ident!("v{}", i),
        };
        let name_1 = format_ident!("{}_1", name_base);
        let name_2 = format_ident!("{}_2", name_base);

        let cmp_expr = quote! {
            let ord = ::core::cmp::Ord::cmp(#name_1, #name_2);
            if ord.is_ne() { return ord; }
        };

        let body = acc.body;
        acc.body = quote! { #body #cmp_expr };
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

pub(crate) fn discriminant_arms(variants: &Punctuated<Variant, Token![,]>) -> TokenStream {
    let initial_discr = LitInt::new("0", proc_macro::Span::def_site().into());
    let initial_discr = Expr::Lit(ExprLit { lit: Lit::Int(initial_discr), attrs: Vec::new() });
    let mut discr_offset = 0;
    let mut last_discr: &Expr = &initial_discr;
    variants
        .iter()
        .map(|v| {
            let ident = &v.ident;
            if let Some((_, discriminant)) = &v.discriminant {
                last_discr = discriminant;
                discr_offset = 0;
            }
            let span = proc_macro::Span::def_site().into();
            let discr_offset_expr = LitInt::new(&discr_offset.to_string(), span);
            let discr_offset_expr = ExprLit { lit: Lit::Int(discr_offset_expr), attrs: Vec::new() };
            let discr_offset_expr = Expr::Lit(discr_offset_expr);
            let res = match &v.fields {
                Fields::Named(_) => quote! {
                    Self::#ident{ .. } => (#last_discr) + #discr_offset_expr,
                },
                Fields::Unnamed(_) => quote! {
                    Self::#ident( .. ) => (#last_discr) + #discr_offset_expr,
                },
                Fields::Unit => quote! {
                    Self::#ident => (#last_discr) + #discr_offset_expr,
                },
            };
            discr_offset += 1;
            res
        })
        .collect()
}
