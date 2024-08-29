extern crate proc_macro;

use proc_macro::TokenStream as TS1;

#[proc_macro_attribute]
pub fn requires(precondition: TS1, tokens: TS1) -> TS1 {
    let tokens = proc_macro2::TokenStream::from(tokens);
    let mut precondition = precondition.to_string();
    precondition = precondition.replace('\n', "\n> > ");
    precondition = format!("> > ```\n> > {precondition}\n> > ```");
    quote::quote! {
        #[cfg_attr(not(doctest), doc = "> <span style=\"color:Tomato;\">requires</span>")]
        #[cfg_attr(not(doctest), doc = #precondition)]
        #tokens
    }
    .into()
}

#[proc_macro_attribute]
pub fn ensures(postcondition: TS1, tokens: TS1) -> TS1 {
    let tokens = proc_macro2::TokenStream::from(tokens);
    let mut postcondition = postcondition.to_string();
    postcondition = postcondition.replace('\n', "\n> > ");
    postcondition = format!("> > ```\n> > {postcondition}\n> > ```");
    quote::quote! {
        #[cfg_attr(not(doctest), doc = "> <span style=\"color:DodgerBlue;\">ensures</span>")]
        #[cfg_attr(not(doctest), doc = #postcondition)]
        #tokens
    }
    .into()
}

#[proc_macro_attribute]
pub fn variant(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro_attribute]
pub fn invariant(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro]
pub fn proof_assert(_: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro]
pub fn snapshot(_: TS1) -> TS1 {
    quote::quote! { creusot_contracts::snapshot::Snapshot::from_fn(|| std::process::abort()) }
        .into()
}

#[proc_macro]
pub fn ghost(body: TS1) -> TS1 {
    let body = proc_macro2::TokenStream::from(body);
    quote::quote! { GhostBox::from_fn(|| { #body }) }.into()
}

#[proc_macro_attribute]
pub fn terminates(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro_attribute]
pub fn pure(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro_attribute]
pub fn logic(_: TS1, _: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro]
pub fn pearlite(_: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro_attribute]
pub fn predicate(_: TS1, _: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro_attribute]
pub fn law(_: TS1, _: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro_attribute]
pub fn trusted(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro]
pub fn extern_spec(_: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro_attribute]
pub fn maintains(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro_attribute]
pub fn open(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro_derive(DeepModel, attributes(DeepModelTy))]
pub fn derive_deep_model(_: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro_derive(Resolve)]
pub fn derive_resolve(_: TS1) -> TS1 {
    TS1::new()
}
