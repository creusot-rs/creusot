use proc_macro::TokenStream as TS1;
use proc_macro2::TokenStream as TS2;
use quote::{ToTokens as _, quote};
use syn::{
    self, Attribute, ItemConst, Token,
    parse::{Error, Parse, ParseStream},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
};

pub enum ConstantArg {
    Eval,
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
        } else {
            Err(Error::new(
                ident.span(),
                "Unexpected `#[constant]` argument: expected `eval`",
            ))
        }
    }
}

impl ConstantArg {
    pub fn to_attr(self) -> Attribute {
        match self {
            ConstantArg::Eval => parse_quote! { #[creusot::eval_constant] },
        }
    }

    fn to_tokens(self) -> TS2 {
        self.to_attr().to_token_stream()
    }
}
