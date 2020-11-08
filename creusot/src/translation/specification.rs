use proc_macro2::TokenStream;
use rustc_middle::mir::Body;
use syn::Term::*;

use syn::*;

use quote::quote;

use syn::Term::*;

pub fn requires_to_why<'tcx>(body: &Body<'tcx>, attr_val: String) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();

    let args = body
        .args_iter()
        .map(|l| syn::Ident::new(format!("{:?}_o", l).as_ref(), syn::export::Span::call_site()));

    let params =
        body.var_debug_info.iter().take(body.arg_count).map(|vdi| {
            syn::Ident::new(vdi.name.to_string().as_ref(), syn::export::Span::call_site())
        });

    let toks = pred_to_why(&p);
    format!(
        "{}",
        quote! {
          let f #(#params)* = #toks in f #(#args)*
        }
    )
}

pub fn ensures_to_why<'tcx>(body: &Body<'tcx>, attr_val: String) -> String {
    requires_to_why(body, attr_val)
}
fn pred_to_why(p: &Term) -> TokenStream {
    match p {
        Binary(TermBinary { left, right, op, .. }) => {
            let left_toks = pred_to_why(&*left);
            let right_toks = pred_to_why(&*right);
            quote! { #left_toks #op #right_toks }
        }
        Impl(TermImpl { hyp, cons, .. }) => {
            let hyp_toks = pred_to_why(&*hyp);
            let cons_toks = pred_to_why(&*cons);

            quote! { #hyp_toks -> #cons_toks }
        }
        Term::Lit(TermLit { lit }) => {
            quote! { #lit }
        }
        Path(p) => {
            if p.path.segments.len() == 1 {
                quote! { #p }
            } else {
                unimplemented!()
            }
        }
        // Call(TermCall {}) => {}
        // If(TermIf {}) => {}
        // Let(TermLet {}) => {}
        // Match(TermMatch{}) => {}
        // Paren(TermParen {}) => {}
        // Tuple(TermTuple {}) => {}
        // Unary(TermUnary {}) => {}
        _ => {
            unimplemented!("{:?}", p);
        }
    }
}
