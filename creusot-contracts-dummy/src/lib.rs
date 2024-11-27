extern crate proc_macro;

mod ghost;

use proc_macro::TokenStream as TS1;

#[proc_macro_attribute]
pub fn requires(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

#[proc_macro_attribute]
pub fn ensures(_: TS1, tokens: TS1) -> TS1 {
    tokens
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
    quote::quote! { ::creusot_contracts::snapshot::Snapshot::from_fn(|| std::process::abort()) }
        .into()
}

#[proc_macro]
pub fn ghost(body: TS1) -> TS1 {
    let body = proc_macro2::TokenStream::from(ghost::ghost_preprocess(body));
    quote::quote! { ::creusot_contracts::ghost::GhostBox::from_fn(|| { #body }) }.into()
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

#[proc_macro_attribute]
pub fn open_inv_result(_: TS1, tokens: TS1) -> TS1 {
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
