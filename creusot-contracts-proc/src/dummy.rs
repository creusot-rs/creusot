use proc_macro::TokenStream as TS1;
use quote::ToTokens as _;
use syn::visit_mut::VisitMut;

// #[proc_macro]

pub fn pearlite(_: TS1) -> TS1 {
    TS1::new()
}

pub fn proof_assert(_: TS1) -> TS1 {
    TS1::new()
}

pub fn snapshot(_: TS1) -> TS1 {
    quote::quote! { ::creusot_contracts::snapshot::Snapshot::from_fn(|| std::process::abort()) }
        .into()
}

pub fn ghost(body: TS1) -> TS1 {
    let body = proc_macro2::TokenStream::from(crate::ghost::ghost_preprocess(body));
    quote::quote! { if false {
        ::creusot_contracts::ghost::Ghost::new({ #body })
    } else {
        ::creusot_contracts::ghost::Ghost::conjure()
    } }
    .into()
}

// #[proc_macro_attribute]

pub fn requires(_: TS1, tokens: TS1) -> TS1 {
    let mut item = syn::parse_macro_input!(tokens as syn::ImplItemFn);
    delete_invariants(&mut item);
    TS1::from(item.into_token_stream())
}

pub fn ensures(_: TS1, tokens: TS1) -> TS1 {
    let mut item = syn::parse_macro_input!(tokens as syn::ImplItemFn);
    delete_invariants(&mut item);
    TS1::from(item.into_token_stream())
}

pub fn variant(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn invariant(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn terminates(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn pure(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn logic(_: TS1, _: TS1) -> TS1 {
    TS1::new()
}

pub fn predicate(_: TS1, _: TS1) -> TS1 {
    TS1::new()
}

pub fn law(_: TS1, _: TS1) -> TS1 {
    TS1::new()
}

pub fn trusted(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn extern_spec(_: TS1) -> TS1 {
    TS1::new()
}

pub fn maintains(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn open(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn open_inv_result(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn bitwise_proof(_: TS1, tokens: TS1) -> TS1 {
    tokens
}

pub fn derive_deep_model(_: TS1) -> TS1 {
    TS1::new()
}

pub fn derive_resolve(_: TS1) -> TS1 {
    TS1::new()
}

/// Visitor to delete all `#[invariant]` and `#[creusot_contracts::invariant]`
/// attributes on loops.
struct DeleteInvariants;

impl VisitMut for DeleteInvariants {
    fn visit_expr_for_loop_mut(&mut self, i: &mut syn::ExprForLoop) {
        delete_invariants_attrs(&mut i.attrs);
        syn::visit_mut::visit_expr_for_loop_mut(self, i)
    }

    fn visit_expr_while_mut(&mut self, i: &mut syn::ExprWhile) {
        delete_invariants_attrs(&mut i.attrs);
        syn::visit_mut::visit_expr_while_mut(self, i)
    }

    fn visit_expr_loop_mut(&mut self, i: &mut syn::ExprLoop) {
        delete_invariants_attrs(&mut i.attrs);
        syn::visit_mut::visit_expr_loop_mut(self, i)
    }
}

// `invariant` or `creusot_contracts::invariant` or `::creusot_contracts::invariant`
fn is_invariant(path: &syn::Path) -> bool {
    if path.is_ident("invariant") {
        return true;
    }
    let mut segments = path.segments.iter();
    if let Some(first) = segments.next() {
        if let Some(second) = segments.next() {
            return first.ident == "creusot_contracts" && second.ident == "invariant";
        }
    }
    false
}

fn delete_invariants_attrs(attrs: &mut Vec<syn::Attribute>) {
    attrs.retain(|attr| {
        if let syn::Meta::List(meta) = &attr.meta { !is_invariant(&meta.path) } else { true }
    });
}

fn delete_invariants(item: &mut syn::ImplItemFn) {
    DeleteInvariants.visit_impl_item_fn_mut(item);
}
