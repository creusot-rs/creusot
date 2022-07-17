extern crate proc_macro;

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
pub fn ghost(_: TS1) -> TS1 {
    quote::quote! { creusot_contracts::Ghost::new() }.into()
}

#[proc_macro]
pub fn pearlite(_: TS1) -> TS1 {
    TS1::new()
}

#[proc_macro_attribute]
pub fn logic(_: TS1, _: TS1) -> TS1 {
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
