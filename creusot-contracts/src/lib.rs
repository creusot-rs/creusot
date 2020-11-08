#![feature(stmt_expr_attributes)]
#![feature(register_tool)]
#![register_tool(creusot)]

extern crate proc_macro;

use proc_macro2::TokenStream;

use syn::*;

use quote::quote;

use syn::Term::*;

fn encode_pred(p: Term) -> TokenStream {
    match p {
        // Conj(TermConj { left, right, .. }) => {
        //   let left = encode_pred(*left);
        //   let right = encode_pred(*right);

        //   quote!{
        //     #[creusot::spec="conj"]
        //     ||{
        //       #left
        //       #right
        //     };
        //   }
        // }
        // Disj(TermDisj{ left, right, .. }) => {
        // let left = encode_pred(*left);
        // let right = encode_pred(*right);

        // quote!{
        //   #[creusot::spec="disj"]
        //   ||{
        //     #left
        //     #right
        //   };
        // }    }
        Impl(TermImpl { hyp, cons, .. }) => {
            let left = encode_pred(*hyp);
            let right = encode_pred(*cons);

            quote! {
              #left;
              #right;
              #[creusot::spec="impl"]
              let _ = ||{};
            }
        }
        Binary(TermBinary { left, right, op }) => {
            let _t = TokenStream::new();
            let exp = syn::TermBinary { left, right, op };

            quote! {
               #exp
            }
        }
        Paren(TermParen { expr, .. }) => { encode_pred(*expr) }
        // Neg(TermNeg {}) => { quote! { error_eng } }
        _ => {
            quote! { #p }
        } // _ => { quote! { error_non_exhaustive }}
    }
}

fn pred_to_why(p : &Term) -> TokenStream {
  match p {
      Binary(TermBinary {left, right, op, ..}) => {
        let left_toks = pred_to_why(&*left);
        let right_toks = pred_to_why(&*right);
        quote! { #left_toks #op #right_toks }
      }
      Impl(TermImpl {hyp, cons, .. }) => {
        let hyp_toks = pred_to_why(&*hyp);
        let cons_toks = pred_to_why(&*cons);

        quote! { #hyp_toks -> #cons_toks }
      }
      Term::Lit(TermLit {lit }) => {quote! { #lit }}
      // Call(TermCall {}) => {}
      // If(TermIf {}) => {}
      // Let(TermLet {}) => {}
      // Match(TermMatch{}) => {}
      // Paren(TermParen {}) => {}
      // Tuple(TermTuple {}) => {}
      // Unary(TermUnary {}) => {}
      _ => { unimplemented!() }
    }
}

#[proc_macro_attribute]
pub fn requires(
    attr: proc_macro::TokenStream,
    tokens: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let p: syn::Term = parse_macro_input!(attr);

    let f: ItemFn = parse_macro_input!(tokens);

    let req_name = syn::Ident::new("test", syn::export::Span::call_site());
    // let mut output = TokenStream::new();
    let req_toks = format!("{}", pred_to_why(&p));
    let output = encode_pred(p);

    let mut req_sig = f.sig.clone();
    req_sig.ident = req_name.clone();


    // TODO: Parse and pass down all the function's arguments.
    proc_macro::TokenStream::from(quote! {
      // #[creusot::spec="expr"]
      // #[creusot::spec::requires]
      // #req_sig {
      //   #output
      // }
      #[creusot::spec::requires=#req_toks]
      // #[creusot::spec]
      // #[creusot::spec::requires(#req_name)]
      #f
    })
}

#[proc_macro_attribute]
pub fn ensures(
    attr: proc_macro::TokenStream,
    tokens: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let p: syn::Term = parse_macro_input!(attr);

    let req_name = syn::Ident::new("test2", syn::export::Span::call_site());
    let tokens = TokenStream::from(tokens);
    // let mut output = TokenStream::new();
    let output = encode_pred(p);
    // TODO: Parse and pass down all the function's arguments.
    proc_macro::TokenStream::from(quote! {
      #[creusot::spec="expr"]
      #[creusot::spec::ensures]
      fn #req_name() {
        #output
      }
      #[creusot::spec::ensures(#req_name)]
      #tokens
    })
}
