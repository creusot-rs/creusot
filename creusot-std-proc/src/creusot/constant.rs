use proc_macro::TokenStream as TS1;
use proc_macro2::TokenStream as TS2;
use quote::quote;
use syn::{
    self, ItemConst, Token,
    parse::{Error, Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
};

enum ConstantArg {
    Eval,
    Open,
}

pub fn constant(args: TS1, decl: TS1) -> TS1 {
    let decl = parse_macro_input!(decl as ItemConst);

    let args =
        parse_macro_input!(args with Punctuated<ConstantArg, Token![,]>::parse_separated_nonempty);
    let attrs = args.into_iter().map(ConstantArg::to_tokens).collect::<Vec<_>>();

    quote! {
        #(#attrs)*
        #decl
    }
    .into()
}

impl Parse for ConstantArg {
    fn parse(src: ParseStream) -> syn::Result<Self> {
        let ident = src.parse::<syn::Ident>()?;
        if ident == "eval" {
            Ok(ConstantArg::Eval)
        } else if ident == "open" {
            Ok(ConstantArg::Open)
        } else {
            Err(Error::new(
                ident.span(),
                "Unexpected `#[constant]` argument: expected `eval` or `open`",
            ))
        }
    }
}

impl ConstantArg {
    fn to_tokens(self) -> TS2 {
        match self {
            ConstantArg::Eval => quote! { #[creusot::eval_constant] },
            ConstantArg::Open => quote! { #[creusot::open_constant] },
        }
    }
}
