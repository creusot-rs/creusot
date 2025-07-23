//! Pre-parse pearlite.
//!
//! Some macros accept pearlite rather than Rust. This module converts the
//! latter to the former.
//!
//! For example, `1 + 2` becomes `creusot_contracts::logic::AddLogic::add(Int::new(1), Int::new(2))`.

use pearlite_syn::Term as RT;
use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use syn::{ExprMacro, Pat, PatType, UnOp, spanned::Spanned};

use pearlite_syn::term::*;
use quote::{ToTokens, quote, quote_spanned};
use syn::Lit;

#[derive(Debug)]
pub enum EncodeError {
    LocalErr,
    Unsupported(Span, String),
}

impl EncodeError {
    pub fn into_tokens(self) -> TokenStream {
        match self {
            Self::LocalErr => {
                quote! { compile_error!("LocalErr: what does this even mean?") }
            }
            Self::Unsupported(sp, msg) => {
                let msg = format!("Unsupported expression: {}", msg);
                quote_spanned! { sp=> compile_error!(#msg) }
            }
        }
    }
}

// TODO: Rewrite this as a source to source transform and *then* call ToTokens on the result
pub fn encode_term(term: &RT) -> Result<TokenStream, EncodeError> {
    let sp = term.span();
    match term {
        // It's unclear what to do with macros. Either we translate the parameters, but then
        // it's impossible to handle proc macros whose parameters is not valid pearlite syntax,
        // or we don't translate parameters, but then we let the user write non-pearlite code
        // in pearlite...
        RT::Macro(ExprMacro { mac, .. }) => {
            if ["proof_assert", "pearlite", "seq"].iter().any(|i| mac.path.is_ident(i)) {
                Ok(term.to_token_stream())
            } else {
                Err(EncodeError::Unsupported(
                    term.span(),
                    "macros other than `pearlite!` or `proof_assert!` or `seq!` are unsupported in pearlite code".into(),
                ))
            }
        }
        RT::Array(_) => Err(EncodeError::Unsupported(term.span(), "Array".into())),
        RT::Binary(TermBinary { left, op, right }) => {
            let mut left = left;
            let mut right = right;

            use syn::BinOp::*;
            if matches!(
                op,
                Eq(_)
                    | Ne(_)
                    | Ge(_)
                    | Le(_)
                    | Gt(_)
                    | Lt(_)
                    | Add(_)
                    | Sub(_)
                    | Mul(_)
                    | Div(_)
                    | Rem(_)
            ) {
                left = match &**left {
                    RT::Paren(TermParen { expr, .. }) => expr,
                    _ => left,
                };
                right = match &**right {
                    RT::Paren(TermParen { expr, .. }) => expr,
                    _ => right,
                };
            }

            let left = encode_term(left)?;
            let right = encode_term(right)?;
            match op {
                Eq(_) => {
                    Ok(quote_spanned! {sp=> ::creusot_contracts::__stubs::equal(#left, #right) })
                }
                Ne(_) => {
                    Ok(quote_spanned! {sp=> ::creusot_contracts::__stubs::neq(#left, #right) })
                }
                Lt(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::lt_log(#left, #right) },
                ),
                Le(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::le_log(#left, #right) },
                ),
                Ge(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::ge_log(#left, #right) },
                ),
                Gt(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::gt_log(#left, #right) },
                ),
                Add(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::AddLogic::add(#left, #right) },
                ),
                Sub(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::SubLogic::sub(#left, #right) },
                ),
                Mul(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::MulLogic::mul(#left, #right) },
                ),
                Div(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::DivLogic::div(#left, #right) },
                ),
                Rem(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::RemLogic::rem(#left, #right) },
                ),
                _ => Ok(quote_spanned! {sp=> #left #op #right }),
            }
        }
        RT::Block(TermBlock { block, .. }) => Ok(encode_block(block)),
        RT::Call(TermCall { func, args, .. }) => {
            let args: Vec<_> = args.into_iter().map(encode_term).collect::<Result<_, _>>()?;
            if let RT::Path(p) = &**func {
                if p.inner.path.is_ident("old") {
                    return Ok(
                        quote_spanned! {sp=> *::creusot_contracts::__stubs::old( #(#args),* ) },
                    );
                }
            }

            let func = encode_term(func)?;
            Ok(quote_spanned! {sp=> #func (#(#args),*)})
        }
        RT::Cast(TermCast { expr, as_token, ty }) => {
            let expr_token = encode_term(expr)?;
            Ok(quote_spanned! {sp=> #expr_token #as_token  #ty})
        }
        RT::Field(TermField { base, member, .. }) => {
            let base = encode_term(base)?;
            Ok(quote!({ #base . #member }))
        }
        RT::Group(TermGroup { expr, .. }) => {
            let term = encode_term(expr)?;
            let mut res = TokenStream::new();
            res.extend_one(TokenTree::Group(Group::new(Delimiter::None, term)));
            Ok(res)
        }
        RT::If(TermIf { cond, then_branch, else_branch, .. }) => {
            let cond = if let RT::Paren(TermParen { expr, .. }) = &**cond
                && matches!(&**expr, RT::Quant(_))
            {
                &**expr
            } else {
                cond
            };
            let cond = encode_term(cond)?;
            let then_branch: Vec<_> =
                then_branch.stmts.iter().map(encode_stmt).collect::<Result<_, _>>()?;
            let else_branch = match else_branch {
                Some((_, t)) => {
                    let term = encode_term(t)?;
                    Some(quote_spanned! {sp=> else #term })
                }
                None => None,
            };
            Ok(quote_spanned! {sp=> if #cond { #(#then_branch)* } #else_branch })
        }
        RT::Index(TermIndex { expr, index, .. }) => {
            let expr = if let RT::Paren(TermParen { expr, .. }) = &**expr { &**expr } else { expr };

            let expr = encode_term(expr)?;
            let index = encode_term(index)?;

            Ok(quote! {
                (#expr).index_logic(#index)
            })
        }
        RT::Let(_) => Err(EncodeError::Unsupported(term.span(), "Let".into())),
        RT::Lit(TermLit { lit: lit @ Lit::Int(int) }) if int.suffix() == "" => {
            // FIXME: allow unbounded integers
            Ok(quote_spanned! {sp=> ::creusot_contracts::model::View::view(#lit as i128) })
        }
        RT::Lit(TermLit { lit: Lit::Int(int) }) if int.suffix() == "int" => {
            let lit = syn::LitInt::new(int.base10_digits(), int.span());
            Ok(quote_spanned! {sp=> ::creusot_contracts::model::View::view(#lit as i128) })
        }
        RT::Lit(TermLit { lit }) => Ok(quote_spanned! {sp=> #lit }),
        RT::Match(TermMatch { expr, arms, .. }) => {
            let arms: Vec<_> = arms.iter().map(encode_arm).collect::<Result<_, _>>()?;
            let expr = encode_term(expr)?;
            Ok(quote_spanned! {sp=> match #expr { #(#arms)* } })
        }
        RT::MethodCall(TermMethodCall { receiver, method, turbofish, args, .. }) => {
            let receiver = encode_term(receiver)?;
            let args: Vec<_> = args.into_iter().map(encode_term).collect::<Result<_, _>>()?;

            Ok(quote_spanned! {sp=> #receiver . #method #turbofish ( #(#args),*) })
        }
        RT::Paren(TermParen { paren_token, expr }) => {
            let mut tokens = TokenStream::new();
            let term = encode_term(expr)?;
            paren_token.surround(&mut tokens, |tokens| {
                tokens.extend(term);
            });
            Ok(tokens)
        }
        RT::Path(_) => Ok(quote_spanned! {sp=> #term }),
        RT::Range(_) => Err(EncodeError::Unsupported(term.span(), "Range".into())),
        RT::Reference(TermReference { mutability, expr, .. }) => {
            let term = encode_term(expr)?;
            Ok(quote_spanned! {sp=>
                & #mutability #term
            })
        }
        RT::Repeat(_) => Err(EncodeError::Unsupported(term.span(), "Repeat".into())),
        RT::Struct(TermStruct { path, fields, rest, brace_token, dot2_token }) => {
            let mut ts = TokenStream::new();
            path.to_tokens(&mut ts);

            let mut inner = TokenStream::new();

            for p in fields.pairs() {
                let (tv, punc) = p.into_tuple();

                tv.member.to_tokens(&mut inner);
                if let Some(colon) = tv.colon_token {
                    colon.to_tokens(&mut inner);
                    inner.extend(encode_term(&tv.expr)?)
                }
                punc.to_tokens(&mut inner);
            }

            brace_token.surround(&mut ts, |tokens| {
                tokens.extend(inner);

                if let Some(dot2_token) = &dot2_token {
                    dot2_token.to_tokens(tokens);
                } else if rest.is_some() {
                    syn::Token![..](Span::call_site()).to_tokens(tokens);
                }
                rest.to_tokens(tokens);
            });

            Ok(ts)
        }
        RT::Tuple(TermTuple { elems, .. }) => {
            if elems.is_empty() {
                return Ok(quote_spanned! {sp=> () });
            }
            let elems: Vec<_> = elems.into_iter().map(encode_term).collect::<Result<_, _>>()?;
            Ok(quote_spanned! {sp=> (#(#elems),*,) })
        }
        RT::Type(ty) => Ok(quote_spanned! {sp=> #ty }),
        RT::Unary(TermUnary { op, expr }) => {
            let term = encode_term(expr)?;
            if matches!(op, UnOp::Neg(_)) {
                Ok(quote_spanned! {sp=> ::creusot_contracts::logic::ops::NegLogic::neg(#term) })
            } else {
                Ok(quote_spanned! {sp=>
                    #op #term
                })
            }
        }
        RT::Final(TermFinal { term, .. }) => {
            let term = encode_term(term)?;
            Ok(quote_spanned! {sp=>
                * ::creusot_contracts::__stubs::fin(#term)
            })
        }
        RT::Model(TermModel { term, .. }) => {
            let term = match &**term {
                RT::Paren(TermParen { expr, .. }) => expr,
                _ => term,
            };
            let term = encode_term(term)?;
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::model::View::view(#term)
            })
        }
        RT::LogEq(TermLogEq { lhs, rhs, .. }) => {
            let lhs = encode_term(lhs)?;
            let rhs = encode_term(rhs)?;
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::equal(#lhs, #rhs)
            })
        }
        RT::Impl(TermImpl { hyp, cons, .. }) => {
            let hyp = match &**hyp {
                Term::Paren(TermParen { expr, .. }) => match &**expr {
                    Term::Quant(_) => expr,
                    _ => hyp,
                },
                _ => hyp,
            };
            let hyp = encode_term(hyp)?;
            let cons = encode_term(cons)?;
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::implication(#hyp, #cons)
            })
        }
        RT::Quant(TermQuant { quant_token, args, trigger, term, .. }) => {
            let mut ts = encode_term(term)?;
            let args_ref = args.iter().map(|QuantArg { ident, ty }| match ty {
                None => quote! { &#ident: &_ },
                Some((_, ty)) => quote! { &#ident: &#ty },
            });
            ts = encode_trigger(trigger, ts)?;
            ts = quote_spanned! {sp=>
                ::creusot_contracts::__stubs::#quant_token(
                    #[creusot::no_translate]
                    #[creusot::logic_closure]
                    |#(#args_ref,)*| { #ts }
                )
            };
            Ok(ts)
        }
        RT::Dead(_) => Ok(quote_spanned! {sp=> *::creusot_contracts::__stubs::dead() }),
        RT::Pearlite(term) => Ok(quote_spanned! {sp=> #term }),
        RT::Closure(clos) => {
            if clos.inputs.len() != 1 {
                return Err(EncodeError::Unsupported(
                    term.span(),
                    "logic closures can only have one parameter".into(),
                ));
            }

            let input = match &clos.inputs[0] {
                Pat::Type(PatType { attrs, pat, ty, .. }) => quote! { #(#attrs)* &#pat : &#ty},
                _ => {
                    let pat = &clos.inputs[0];
                    quote! { &#pat }
                }
            };

            let retty = &clos.output;
            let clos = encode_term(&clos.body)?;
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::mapping_from_fn(
                    #[creusot::no_translate] #[creusot::logic_closure] |#input| #retty #clos)
            })
        }
        RT::__Nonexhaustive => todo!(),
    }
}

fn encode_trigger(
    mut trigger: &[Trigger],
    mut ts: TokenStream,
) -> Result<TokenStream, EncodeError> {
    while let [rest @ .., last] = trigger {
        trigger = rest;
        let trigs = last.terms.iter().map(encode_term).collect::<Result<Vec<_>, _>>()?;
        ts = quote!(::creusot_contracts::__stubs::trigger((#(#trigs,)*), #ts))
    }
    Ok(ts)
}

pub fn encode_block(block: &TBlock) -> TokenStream {
    // If there are errors during encode_stmt, still emit the braces
    // to allow the parser to skip over the body and discover more errors.
    let mut tokens = TokenStream::new();
    block.brace_token.surround(&mut tokens, |tokens| {
        block.stmts.iter().for_each(|stmt| {
            encode_stmt(stmt).unwrap_or_else(|e| e.into_tokens()).to_tokens(tokens)
        })
    });
    tokens
}

pub fn encode_stmt(stmt: &TermStmt) -> Result<TokenStream, EncodeError> {
    match stmt {
        TermStmt::Local(TLocal { let_token, pat, init, semi_token }) => {
            if let Some((eq_token, init)) = init {
                let pat = encode_pattern(pat)?;
                let init = encode_term(init)?;
                Ok(quote! { #let_token #pat #eq_token #init #semi_token })
            } else {
                Err(EncodeError::LocalErr)
            }
        }
        TermStmt::Expr(e) => encode_term(e),
        TermStmt::Semi(t, s) => {
            let term = encode_term(t)?;
            Ok(quote! { #term #s })
        }
        TermStmt::Item(i) => Ok(quote! { #i }),
        TermStmt::Empty(s) => Ok(quote! { #s }),
    }
}

fn encode_pattern(pat: &Pat) -> Result<TokenStream, EncodeError> {
    Ok(quote! { #pat })
}

fn encode_arm(arm: &TermArm) -> Result<TokenStream, EncodeError> {
    let body = encode_term(&arm.body)?;
    let pat = &arm.pat;
    // let (if_tok, guard) = arm.guard;
    let comma = arm.comma;
    Ok(quote! { #pat  => #body #comma })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_old() {
        let term: Term = syn::parse_str("old(x)").unwrap();

        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            "* :: creusot_contracts :: __stubs :: old (x)"
        );
    }

    #[test]
    fn encode_fin() {
        let term: Term = syn::parse_str("^ x").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            "* :: creusot_contracts :: __stubs :: fin (x)"
        );

        let term: Term = syn::parse_str("^ ^ x").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            "* :: creusot_contracts :: __stubs :: fin (* :: creusot_contracts :: __stubs :: fin (x))"
        );
    }

    #[test]
    fn encode_cur() {
        let term: Term = syn::parse_str("* x").unwrap();
        assert_eq!(format!("{}", encode_term(&term).unwrap()), "* x");
        let term: Term = syn::parse_str("* ^ x").unwrap();

        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            "* * :: creusot_contracts :: __stubs :: fin (x)"
        );
    }

    #[test]
    fn encode_forall() {
        let term: Term = syn::parse_str("forall<x: Int> x == x").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            ":: creusot_contracts :: __stubs :: forall (# [creusot :: no_translate] | x : Int | { :: creusot_contracts :: __stubs :: equal (x , x) })"
        );

        let term: Term = syn::parse_str("forall<x: Int> forall<y: Int> true").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            ":: creusot_contracts :: __stubs :: forall (# [creusot :: no_translate] | x : Int | { :: creusot_contracts :: __stubs :: forall (# [creusot :: no_translate] | y : Int | { true }) })"
        );
    }

    #[test]
    fn encode_exists() {
        let term: Term = syn::parse_str("exists<x:Int> x == x").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            ":: creusot_contracts :: __stubs :: exists (# [creusot :: no_translate] | x : Int | { :: creusot_contracts :: __stubs :: equal (x , x) })"
        );

        let term: Term = syn::parse_str("exists<x:Int> exists<y:Int> true").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            ":: creusot_contracts :: __stubs :: exists (# [creusot :: no_translate] | x : Int | { :: creusot_contracts :: __stubs :: exists (# [creusot :: no_translate] | y : Int | { true }) })"
        );
    }

    #[test]
    fn encode_impl() {
        let term: Term = syn::parse_str("false ==> true").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            ":: creusot_contracts :: __stubs :: implication (false , true)"
        );
    }
}
