use pearlite_syn::Term as RT;
use proc_macro2::TokenStream;
use syn::Pat;

use pearlite_syn::term::*;
use quote::quote;
use syn::Lit;

#[derive(Debug)]
pub enum EncodeError {
    LocalErr,
}

pub fn encode_term(term: RT) -> Result<TokenStream, EncodeError> {
    match term {
        RT::Array(_) => todo!("Array"),
        RT::Binary(TermBinary { left, op, right }) => {
            let left = encode_term(*left)?;
            let right = encode_term(*right)?;

            Ok(quote! { #left #op #right })
        }
        RT::Block(TermBlock { block, .. }) => {
            let stmts: Vec<_> =
                block.stmts.into_iter().map(encode_stmt).collect::<Result<_, _>>()?;

            Ok(quote! {
                {
                    #(#stmts)*
                }
            })
        }
        RT::Call(TermCall { func, args, .. }) => {
            let func = encode_term(*func)?;

            let args: Vec<_> = args.into_iter().map(encode_term).collect::<Result<_, _>>()?;

            Ok(quote! { #func (#(#args),*)})
        }
        RT::Cast(_) => todo!("Cast"),
        RT::Field(TermField { base, member, .. }) => {
            let base = encode_term(*base)?;

            Ok(quote!({ #base . #member }))
        }
        RT::Group(_) => todo!("Group"),
        RT::If(TermIf { cond, then_branch, else_branch, .. }) => {
            let cond = encode_term(*cond)?;
            let then_branch: Vec<_> =
                then_branch.stmts.into_iter().map(encode_stmt).collect::<Result<_, _>>()?;
            let else_branch = match else_branch {
                Some((_, t)) => {
                    let term = encode_term(*t)?;
                    Some(quote! { else #term })
                }
                None => None,
            };

            Ok(quote! {
                if #cond { #(#then_branch)* } #else_branch
            })
        }
        RT::Index(_) => todo!("Index"),
        RT::Let(_) => todo!("Let"),
        RT::Lit(TermLit { ref lit }) => match lit {
            Lit::Int(int) if int.suffix() == "" => Ok(quote! { Int::from(#lit) }),
            _ => Ok(quote! { #lit }),
        },
        RT::Match(TermMatch { expr, arms, .. }) => {
            let arms: Vec<_> = arms.into_iter().map(encode_arm).collect::<Result<_, _>>()?;
            let expr = encode_term(*expr)?;

            Ok(quote! {
                match #expr {
                    #(#arms)*
                }
            })
        }
        RT::MethodCall(TermMethodCall { receiver, method, turbofish, args, .. }) => {
            let receiver = encode_term(*receiver)?;
            let args: Vec<_> = args.into_iter().map(encode_term).collect::<Result<_, _>>()?;

            Ok(quote! {
                #receiver . #method #turbofish ( #(#args),*)
            })
        }
        RT::Paren(TermParen { expr, .. }) => {
            let term = encode_term(*expr)?;
            Ok(quote! { (#term ) })
        }
        RT::Path(_) => Ok(quote! { #term }),
        RT::Range(_) => todo!("Range"),
        RT::Repeat(_) => todo!("Repeat"),
        RT::Struct(_) => todo!("Struct"),
        RT::Tuple(TermTuple { elems, .. }) => {
            let elems: Vec<_> = elems.into_iter().map(encode_term).collect::<Result<_, _>>()?;

            Ok(quote! {
                (#(#elems),*)
            })
        }
        RT::Type(ty) => Ok(quote! { #ty }),
        RT::Unary(TermUnary { op, expr }) => {
            let term = encode_term(*expr)?;
            Ok(quote! {
              #op #term
            })
        }
        RT::Final(TermFinal { term, .. }) => {
            let term = encode_term(*term)?;
            Ok(quote! {
              creusot_contracts::stubs::fin(#term)
            })
        }
        RT::Verbatim(_) => todo!(),
        RT::LogEq(TermLogEq { lhs, rhs, .. }) => {
            let lhs = encode_term(*lhs)?;
            let rhs = encode_term(*rhs)?;
            Ok(quote! {
                creusot_contracts::stubs::equal(#lhs, #rhs)
            })
        }
        RT::Impl(TermImpl { hyp, cons, .. }) => {
            let hyp = encode_term(*hyp)?;
            let cons = encode_term(*cons)?;
            Ok(quote! {
                creusot_contracts::stubs::implication(#hyp, #cons)
            })
        }
        RT::Forall(TermForall { args, term, .. }) => {
            let mut ts = encode_term(*term)?;
            for arg in args {
                ts = quote! {
                    creusot_contracts::stubs::forall(
                        #[creusot::spec::no_translate]
                        |#arg|{ #ts }
                    )
                }
            }
            Ok(ts)
        }
        RT::Exists(TermExists { args, term, .. }) => {
            let mut ts = encode_term(*term)?;
            for arg in args {
                ts = quote! {
                    creusot_contracts::stubs::exists(
                        #[creusot::spec::no_translate]
                        |#arg|{ #ts }
                    )
                }
            }
            Ok(ts)
        }
        RT::Absurd(_) => Ok(quote! { creusot_contracts::stubs::abs() }),
        RT::__Nonexhaustive => todo!(),
    }
}

fn encode_stmt(stmt: TermStmt) -> Result<TokenStream, EncodeError> {
    match stmt {
        TermStmt::Local(TLocal { pat, init, .. }) => {
            if let Some((_, init)) = init {
                let pat = encode_pattern(pat)?;
                let init = encode_term(*init)?;
                Ok(quote! { let #pat = #init ; })
            } else {
                Err(EncodeError::LocalErr)
            }
        }
        TermStmt::Expr(e) => encode_term(e),
        TermStmt::Semi(t, s) => {
            let term = encode_term(t)?;
            Ok(quote! { #term #s })
        }
    }
}

fn encode_pattern(pat: Pat) -> Result<TokenStream, EncodeError> {
    Ok(quote! { #pat })
}

fn encode_arm(arm: TermArm) -> Result<TokenStream, EncodeError> {
    let body = encode_term(*arm.body)?;
    let pat = arm.pat;
    // let (if_tok, guard) = arm.guard;
    let comma = arm.comma;
    Ok(quote! { #pat  => #body #comma })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_fin() {
        let term: Term = syn::parse_str("^ x").unwrap();
        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "creusot_contracts :: stubs :: fin (x)"
        );

        let term: Term = syn::parse_str("^ ^ x").unwrap();
        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "creusot_contracts :: stubs :: fin (creusot_contracts :: stubs :: fin (x))"
        );
    }

    #[test]
    fn encode_cur() {
        let term: Term = syn::parse_str("* x").unwrap();
        assert_eq!(format!("{}", encode_term(term).unwrap()), "* x");
        let term: Term = syn::parse_str("* ^ x").unwrap();

        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "* creusot_contracts :: stubs :: fin (x)"
        );
    }

    #[test]
    fn encode_forall() {
        let term: Term = syn::parse_str("forall<x:Int> x == x").unwrap();
        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "creusot_contracts :: stubs :: forall (# [creusot :: spec :: no_translate] | x : Int | { x == x })"
        );

        let term: Term = syn::parse_str("forall<x:Int> forall<y:Int> y == x || y != x").unwrap();
        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "creusot_contracts :: stubs :: forall (# [creusot :: spec :: no_translate] | x : Int | { creusot_contracts :: stubs :: forall (# [creusot :: spec :: no_translate] | y : Int | { y == x || y != x }) })"
        );
    }

    #[test]
    fn encode_exists() {
        let term: Term = syn::parse_str("exists<x:Int> x == x").unwrap();
        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "creusot_contracts :: stubs :: exists (# [creusot :: spec :: no_translate] | x : Int | { x == x })"
        );

        let term: Term = syn::parse_str("exists<x:Int> exists<y:Int> y == x || y != x").unwrap();
        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "creusot_contracts :: stubs :: exists (# [creusot :: spec :: no_translate] | x : Int | { creusot_contracts :: stubs :: exists (# [creusot :: spec :: no_translate] | y : Int | { y == x || y != x }) })"
        );
    }

    #[test]
    fn encode_impl() {
        let term: Term = syn::parse_str("false ==> true").unwrap();
        assert_eq!(
            format!("{}", encode_term(term).unwrap()),
            "creusot_contracts :: stubs :: implication (false , true)"
        );
    }
}
