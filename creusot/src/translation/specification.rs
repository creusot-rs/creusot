use std::collections::HashSet;

use proc_macro2::TokenStream;
use rustc_middle::mir::{Body, SourceInfo};
use syn::{visit::Visit, Term::*};

use syn::*;

use quote::quote;

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

pub fn invariant_to_why<'tcx>(body: &Body<'tcx>, info: SourceInfo, attr_val: String) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    let fvs = FreeVars::for_term(&p);

    let vars_in_scope: Vec<_> =
        body.var_debug_info.iter().filter(|vdi| vdi.source_info.scope <= info.scope).collect();

    // TODO: ensure only one match
    let lcls = fvs.iter().map(|free| {
        let var_info =
            vars_in_scope.iter().filter(|vdi| *free == vdi.name.to_ident_string()).next().unwrap();

        let loc = var_info.place.as_local().unwrap();
        syn::Ident::new(format!("{:?}", loc).as_ref(), syn::export::Span::call_site())
    });

    let toks = pred_to_why(&p);
    let fv_iter = fvs.iter();

    format!(
        "{}",
        quote! {
            let f #(#fv_iter)* = #toks in f #(#lcls)*
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
        Paren(TermParen { expr, .. }) => {
            let ttoks = pred_to_why(expr);
            quote! { ( #ttoks ) }
        }
        // Call(TermCall {}) => {}
        // If(TermIf {}) => {}
        // Let(TermLet {}) => {}
        // Match(TermMatch{}) => {}
        // Tuple(TermTuple {}) => {}
        // Unary(TermUnary {}) => {}
        _ => {
            unimplemented!("{:?}", p);
        }
    }
}

struct FreeVars {
    free: HashSet<syn::Ident>,
    bound: HashSet<syn::Ident>,
}

// TODO: Rewrite / clarify scoping rules.
impl<'ast> Visit<'ast> for FreeVars {
    fn visit_term_path(&mut self, i: &'ast TermPath) {
        // variable
        if i.path.segments.len() == 1 {
            self.free.insert(i.path.segments[0].ident.clone());
        }
    }

    // Scoping.
    fn visit_tblock(&mut self, i: &'ast TBlock) {
        let mut bound_in_block = self.bound.clone();
        for term in &i.stmts {
            let mut fv = FreeVars { free: HashSet::new(), bound: HashSet::new() };
            visit::visit_term_stmt(&mut fv, term);
            self.free.extend(&fv.free - &bound_in_block);
            bound_in_block.extend(fv.bound);
        }
    }

    fn visit_term_if(&mut self, i: &'ast TermIf) {
        let mut fv = FreeVars { free: HashSet::new(), bound: HashSet::new() };
        visit::visit_term(&mut fv, &i.cond);
        visit::visit_tblock(&mut fv, &i.then_branch);
        self.free.extend(&fv.free - &fv.bound);

        // if let bindings are only visible in the then branch (obviously)
        if let Some((_, else_branch)) = &i.else_branch {
            let mut fv = FreeVars { free: HashSet::new(), bound: HashSet::new() };
            visit::visit_term(&mut fv, &*else_branch);
            self.free.extend(fv.free);
        }
    }

    // Occurs in if let / while let
    fn visit_term_let(&mut self, i: &'ast TermLet) {
        let mut fv = FreeVars { free: HashSet::new(), bound: HashSet::new() };
        visit::visit_term_let(&mut fv, i);

        let new_free = &fv.free - &self.bound;
        self.free.extend(new_free);
        self.bound.extend(fv.bound);
    }

    fn visit_term_arm(&mut self, i: &'ast TermArm) {
        let mut fv = FreeVars { free: HashSet::new(), bound: HashSet::new() };

        visit::visit_term_arm(&mut fv, i);

        let new_free = &fv.free - &fv.bound;
        self.free.extend(new_free)
    }
    fn visit_pat_ident(&mut self, i: &'ast PatIdent) {
        self.bound.insert(i.ident.clone());
    }
}

impl FreeVars {
    fn for_term(t: &Term) -> HashSet<syn::Ident> {
        // dbg!(t);
        let mut fv = FreeVars { free: HashSet::new(), bound: HashSet::new() };
        fv.visit_term(t);

        &fv.free - &fv.bound
    }
}
