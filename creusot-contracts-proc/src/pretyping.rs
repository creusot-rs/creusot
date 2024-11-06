use pearlite_syn::Term as RT;
use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use syn::{spanned::Spanned, ExprMacro, Pat};

use pearlite_syn::term::*;
use quote::{quote, quote_spanned, ToTokens};
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
                quote! { compile_error!("LocalErr: what does this even mean? -- Xavier") }
            }
            Self::Unsupported(sp, msg) => {
                let msg = format!("Unsupported expression: {}", msg);
                quote_spanned! {sp=> compile_error!(#msg) }
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
            if mac.path.is_ident("proof_assert") || mac.path.is_ident("pearlite") {
                Ok(term.to_token_stream())
            } else {
                Err(EncodeError::Unsupported(
                    term.span(),
                    "Macros other than pearlite! or proof_assert! are unsupported".into(),
                ))
            }
        }
        RT::Array(_) => Err(EncodeError::Unsupported(term.span(), "Array".into())),
        RT::Binary(TermBinary { left, op, right }) => {
            let mut left = left;
            let mut right = right;

            use syn::BinOp::*;
            if matches!(op, Eq(_) | Ne(_) | Ge(_) | Le(_) | Gt(_) | Lt(_)) {
                left = match &**left {
                    RT::Paren(TermParen { expr, .. }) => &expr,
                    _ => &*left,
                };
                right = match &**right {
                    RT::Paren(TermParen { expr, .. }) => &expr,
                    _ => &*right,
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
                _ => Ok(quote_spanned! {sp=> #left #op #right }),
            }
        }
        RT::Block(TermBlock { block, .. }) => encode_block(&block.stmts),
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
        RT::Cast(_) => Err(EncodeError::Unsupported(term.span(), "Cast".into())),
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
            let expr =
                if let RT::Paren(TermParen { expr, .. }) = &**expr { &**expr } else { &*expr };

            let expr = encode_term(expr)?;
            let index = encode_term(index)?;

            Ok(quote! {
                (#expr).index_logic(#index)
            })
        }
        RT::Let(_) => Err(EncodeError::Unsupported(term.span(), "Let".into())),
        RT::Lit(TermLit { ref lit }) => match lit {
            // FIXME: allow unbounded integers
            Lit::Int(int) if int.suffix() == "" => {
                Ok(quote_spanned! {sp=> ::creusot_contracts::model::View::view(#lit as i128) })
            }
            _ => Ok(quote_spanned! {sp=> #lit }),
        },
        RT::Match(TermMatch { expr, arms, .. }) => {
            let arms: Vec<_> = arms.into_iter().map(encode_arm).collect::<Result<_, _>>()?;
            let expr = encode_term(expr)?;
            Ok(quote_spanned! {sp=> match #expr { #(#arms)* } })
        }
        RT::MethodCall(TermMethodCall { receiver, method, turbofish, args, .. }) => {
            let receiver = encode_term(receiver)?;
            let args: Vec<_> = args.into_iter().map(encode_term).collect::<Result<_, _>>()?;

            Ok(quote_spanned! {sp=> #receiver . #method #turbofish ( #(#args),*) })
        }
        RT::Paren(TermParen { expr, .. }) => {
            let term = encode_term(expr)?;
            Ok(quote_spanned! {sp=> (#term) })
        }
        RT::Path(_) => Ok(quote_spanned! {sp=> #term }),
        RT::Range(_) => Err(EncodeError::Unsupported(term.span(), "Range".into())),
        RT::Reference(TermReference { mutability, expr, .. }) => {
            let term = encode_term(expr)?;
            Ok(quote! {
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
            Ok(quote! {
                #op #term
            })
        }
        RT::Final(TermFinal { term, .. }) => {
            let term = encode_term(term)?;
            Ok(quote! {
                * ::creusot_contracts::__stubs::fin(#term)
            })
        }
        RT::Model(TermModel { term, .. }) => {
            let term = match &**term {
                RT::Paren(TermParen { expr, .. }) => &expr,
                _ => &*term,
            };
            let term = encode_term(term)?;
            Ok(quote! {
                ::creusot_contracts::model::View::view(#term)
            })
        }
        RT::Verbatim(_) => todo!(),
        RT::LogEq(TermLogEq { lhs, rhs, .. }) => {
            let lhs = encode_term(lhs)?;
            let rhs = encode_term(rhs)?;
            Ok(quote! {
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
            Ok(quote! {
                ::creusot_contracts::__stubs::implication(#hyp, #cons)
            })
        }
        RT::Quant(TermQuant { quant_token, args, trigger, term, .. }) => {
            let mut ts = encode_term(term)?;
            ts = encode_trigger(&trigger, ts)?;
            ts = quote! {
                ::creusot_contracts::__stubs::#quant_token(
                    #[creusot::no_translate]
                    |#args| { #ts }
                )
            };
            Ok(ts)
        }
        RT::Dead(_) => Ok(quote_spanned! {sp=> *::creusot_contracts::__stubs::dead() }),
        RT::Pearlite(term) => Ok(quote_spanned! {sp=> #term }),
        RT::Closure(clos) => {
            let inputs = &clos.inputs;
            let retty = &clos.output;
            let clos = encode_term(&*clos.body)?;

            Ok(
                quote_spanned! {sp=> ::creusot_contracts::__stubs::mapping_from_fn(#[creusot::no_translate] |#inputs| #retty #clos)},
            )
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
        let mut last_trigger = TokenStream::new();
        for pair in last.terms.pairs() {
            last_trigger.extend(encode_term(pair.value())?);
            pair.punct().to_tokens(&mut last_trigger)
        }
        ts = quote!(::creusot_contracts::__stubs::trigger((#last_trigger), #ts))
    }
    Ok(ts)
}

pub fn encode_block(block: &Vec<TermStmt>) -> Result<TokenStream, EncodeError> {
    let stmts: Vec<_> = block.iter().map(encode_stmt).collect::<Result<_, _>>()?;
    Ok(quote! { { #(#stmts)* } })
}

pub fn encode_stmt(stmt: &TermStmt) -> Result<TokenStream, EncodeError> {
    match stmt {
        TermStmt::Local(TLocal { pat, init, .. }) => {
            if let Some((_, init)) = init {
                let pat = encode_pattern(pat)?;
                let init = encode_term(init)?;
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
        TermStmt::Item(i) => Ok(quote! { #i }),
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
        let term: Term = syn::parse_str("forall<x:Int> x == x").unwrap();
        assert_eq!(
            format!("{}", encode_term(&term).unwrap()),
            ":: creusot_contracts :: __stubs :: forall (# [creusot :: no_translate] | x : Int | { :: creusot_contracts :: __stubs :: equal (x , x) })"
        );

        let term: Term = syn::parse_str("forall<x:Int> forall<y:Int> true").unwrap();
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
