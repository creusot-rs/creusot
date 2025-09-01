//! Pre-parse pearlite.
//!
//! Some macros accept pearlite rather than Rust. This module converts the
//! latter to the former.
//!
//! For example, `1 + 2` becomes `creusot_contracts::logic::AddLogic::add(Int::new(1), Int::new(2))`.

use pearlite_syn::Term as RT;
use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use std::collections::HashSet;
use syn::{
    ExprMacro, Ident, Pat, PatIdent, PatType, UnOp,
    spanned::Spanned,
    visit::{Visit, visit_pat},
};

use pearlite_syn::term::*;
use quote::{ToTokens, quote, quote_spanned};
use syn::Lit;

#[derive(Debug)]
pub enum EncodeError {
    /// A `let` binding is not initialized
    LocalLetNoInit(Span),
    /// Some expression is not supported in pearlite
    Unsupported(Span, String),
}

impl EncodeError {
    pub fn into_tokens(self) -> TokenStream {
        match self {
            Self::LocalLetNoInit(sp) => {
                quote_spanned! { sp => compile_error!("This `let` binding is not initialized") }
            }
            Self::Unsupported(sp, msg) => {
                let msg = format!("Unsupported expression: {}", msg);
                quote_spanned! { sp=> compile_error!(#msg) }
            }
        }
    }
}

struct Locals {
    /// "ref-bound" variables: we replaced their binder with `&x` and their occurrences should be expanded as `*x`.
    /// Other variables are untouched, their occurrences should be expanded as `*&x`.
    refvars: HashSet<Ident>,
    /// Variables to toggle when leaving scopes.
    undo: Vec<Vec<Ident>>,
}

impl Locals {
    fn new() -> Self {
        Locals { refvars: HashSet::new(), undo: vec![vec![]] }
    }

    fn open(&mut self) {
        self.undo.push(vec![])
    }

    fn close(&mut self) {
        for var in self.undo.pop().unwrap().into_iter().rev() {
            use std::collections::hash_set::Entry::*;
            match self.refvars.entry(var) {
                Occupied(entry) => {
                    entry.remove();
                }
                Vacant(entry) => entry.insert(),
            }
        }
    }

    fn bind_ref(&mut self, ident: Ident) {
        if self.refvars.insert(ident.clone()) {
            self.undo.last_mut().unwrap().push(ident)
        }
    }

    fn bind_raw(&mut self, ident: &Ident) {
        if self.refvars.remove(ident) {
            self.undo.last_mut().unwrap().push(ident.clone())
        }
    }

    fn is_ref_bound(&self, ident: &Ident) -> bool {
        self.refvars.contains(ident)
    }
}

pub fn encode_term(term: &RT) -> Result<TokenStream, EncodeError> {
    encode_term_(term, &mut Locals::new())
}

// TODO: Rewrite this as a source to source transform and *then* call ToTokens on the result
fn encode_term_(term: &RT, locals: &mut Locals) -> Result<TokenStream, EncodeError> {
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
                    sp,
                    "macros other than `pearlite!` or `proof_assert!` or `seq!` are unsupported in pearlite code".into(),
                ))
            }
        }
        RT::Array(_) => Err(EncodeError::Unsupported(sp, "Array".into())),
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

            let left = encode_term_(left, locals)?;
            let right = encode_term_(right, locals)?;
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
        RT::Block(TermBlock { block, .. }) => Ok(encode_block_(block, locals)),
        RT::Call(TermCall { func, args, .. }) => {
            let args: Vec<_> =
                args.into_iter().map(|t| encode_term_(t, locals)).collect::<Result<_, _>>()?;
            if let RT::Path(p) = &**func {
                if p.inner.path.is_ident("old") {
                    return Ok(
                        quote_spanned! {sp=> *::creusot_contracts::__stubs::old( #(#args),* ) },
                    );
                }
                // Don't wrap function calls in `*&`.
                return Ok(quote_spanned! {sp=> #func (#(#args),*)});
            } else {
                Err(EncodeError::Unsupported(
                    sp,
                    "(expr)() where (expr) is not an identifier".to_string(),
                ))
            }
        }
        RT::Cast(TermCast { expr, as_token, ty }) => {
            let expr_token = encode_term_(expr, locals)?;
            Ok(quote_spanned! {sp=> #expr_token #as_token  #ty})
        }
        RT::Field(TermField { base, member, .. }) => {
            let base = encode_term_(base, locals)?;
            Ok(quote!({ #base . #member }))
        }
        RT::Group(TermGroup { expr, .. }) => {
            let term = encode_term_(expr, locals)?;
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
            let cond = encode_term_(cond, locals)?;
            let then_branch: Vec<_> = then_branch
                .stmts
                .iter()
                .map(|s| encode_stmt_(s, locals))
                .collect::<Result<_, _>>()?;
            let else_branch = match else_branch {
                Some((_, t)) => {
                    let term = encode_term_(t, locals)?;
                    Some(quote_spanned! {sp=> else #term })
                }
                None => None,
            };
            Ok(quote_spanned! {sp=> if #cond { #(#then_branch)* } #else_branch })
        }
        RT::Index(TermIndex { expr, index, .. }) => {
            let expr = if let RT::Paren(TermParen { expr, .. }) = &**expr { &**expr } else { expr };

            let expr = encode_term_(expr, locals)?;
            let index = encode_term_(index, locals)?;

            Ok(quote! {
                // FIXME: this requires IndexLogic to be loaded
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
            let arms: Vec<_> =
                arms.iter().map(|a| encode_arm_(a, locals)).collect::<Result<_, _>>()?;
            let expr = encode_term_(expr, locals)?;
            Ok(quote_spanned! {sp=> match #expr { #(#arms)* } })
        }
        RT::MethodCall(TermMethodCall { receiver, method, turbofish, args, .. }) => {
            let receiver = encode_term_(receiver, locals)?;
            let args: Vec<_> =
                args.into_iter().map(|t| encode_term_(t, locals)).collect::<Result<_, _>>()?;
            Ok(quote_spanned! {sp=> #receiver . #method #turbofish ( #(#args),*) })
        }
        RT::Paren(TermParen { paren_token, expr }) => {
            let mut tokens = TokenStream::new();
            let term = encode_term_(expr, locals)?;
            paren_token.surround(&mut tokens, |tokens| {
                tokens.extend(term);
            });
            Ok(tokens)
        }
        RT::Path(path) if let Some(ident) = path.inner.path.get_ident() => {
            let term = if locals.is_ref_bound(ident) {
                quote_spanned! { sp=> *#ident }
            } else {
                quote_spanned! { sp=> *&#ident }
            };
            Ok(TokenStream::from(TokenTree::Group(Group::new(Delimiter::Parenthesis, term))))
        }
        RT::Path(path) => Ok(quote_spanned! {sp=> #path}),
        RT::Range(_) => Err(EncodeError::Unsupported(term.span(), "Range".into())),
        RT::Reference(TermReference { mutability, expr, .. }) => {
            let term = encode_term_(expr, locals)?;
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
                    inner.extend(encode_term_(&tv.expr, locals)?)
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
            let elems: Vec<_> =
                elems.into_iter().map(|t| encode_term_(t, locals)).collect::<Result<_, _>>()?;
            Ok(quote_spanned! {sp=> (#(#elems),*,) })
        }
        RT::Type(ty) => Ok(quote_spanned! {sp=> #ty }),
        RT::Unary(TermUnary { op, expr }) => {
            let term = encode_term_(expr, locals)?;
            if matches!(op, UnOp::Neg(_)) {
                Ok(quote_spanned! {sp=> ::creusot_contracts::logic::ops::NegLogic::neg(#term) })
            } else {
                Ok(quote_spanned! {sp=>
                    #op #term
                })
            }
        }
        RT::Final(TermFinal { term, .. }) => {
            let term = encode_term_(term, locals)?;
            Ok(quote_spanned! {sp=>
                * ::creusot_contracts::__stubs::fin(#term)
            })
        }
        RT::Model(TermModel { term, .. }) => {
            let term = match &**term {
                RT::Paren(TermParen { expr, .. }) => expr,
                _ => term,
            };
            let term = encode_term_(term, locals)?;
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::model::View::view(#term)
            })
        }
        RT::LogEq(TermLogEq { lhs, rhs, .. }) => {
            let lhs = encode_term_(lhs, locals)?;
            let rhs = encode_term_(rhs, locals)?;
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
            let hyp = encode_term_(hyp, locals)?;
            let cons = encode_term_(cons, locals)?;
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::implication(#hyp, #cons)
            })
        }
        RT::Quant(TermQuant { quant_token, args, trigger, term, .. }) => {
            locals.open();
            let args_ref = args
                .iter()
                .map(|QuantArg { ident, ty }| {
                    locals.bind_ref(ident.clone());
                    match ty {
                        None => quote! { #ident: &_ },
                        Some((_, ty)) => quote! { #ident: &#ty },
                    }
                })
                .collect::<Vec<_>>();
            let mut ts = encode_term_(term, locals)?;
            ts = encode_trigger_(trigger, ts, locals)?;
            locals.close();
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::#quant_token(
                    #[creusot::no_translate]
                    #[creusot::logic_closure]
                    |#(#args_ref,)*| { #ts }
                )
            })
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
            locals.open();
            // We want to allow mappings of unsized types, like `|x: [usize]| ...`
            // but we can't bind variables of unsized types.
            // - in all cases, wrap the argument type in `&` (`&[usize]`),
            //   because Rust closure arguments must be sized.
            // - this changes the type of `x` (`|x: &[usize]|`),
            //   and we compensate by replacing all occurrences of `x` with `*x`
            //   (this is enabled by calling `locals.bind_ref`).
            //
            // Unfortunately, this idea does not quite work because
            // (1) closure argument binders can be arbitrary patterns, and
            // (2) proc macros can't distinguish variables from nullary enum constructors,
            // so we can't know what variables `var` are bound by a pattern
            // in order to substitute their occurrences in the closure body with `*var`.
            // The danger is that if we naively treat a constructor `C` as a bound variable,
            // adding it to `bind_ref`, its occurrences will become `*C` which is nonsense.
            //
            // We compromise:
            // - we only do the `x` to `*x` substitution for a simple binder `|x|` or `|x: ty|`
            //   (intentionally assuming that `x` is a variable and not a constructor);
            // - for non-variable patterns `|pat|` or `|pat: [usize]|`,
            //   we just don't support unsized variables.
            //   The binder becomes `|&pat: &[usize]|` so the type of `pat` doesn't change
            //   and no substitution is necessary (actually we will replace `x` with `*&x` instead,
            //   which doesn't change the type and works even if `x` is a constructor).
            //
            // Another solution could be to forbid non-variable patterns in Pearlite closures,
            // but I think at least pair patterns `|(x, y)|` could be handy...
            let input = match &clos.inputs[0] {
                // |x: ty|
                Pat::Type(PatType {
                    attrs,
                    pat:
                        box Pat::Ident(PatIdent {
                            by_ref: None,
                            mutability: None,
                            ident,
                            subpat: None,
                            ..
                        }),
                    ty,
                    ..
                }) => {
                    locals.bind_ref(ident.clone());
                    quote! { #(#attrs)* #ident : &#ty }
                }
                // |pat: ty|
                Pat::Type(PatType { attrs, pat, ty, .. }) => {
                    pattern_bind(pat, locals);
                    quote! { #(#attrs)* &#pat : &#ty }
                }
                // |x|
                Pat::Ident(PatIdent {
                    by_ref: None,
                    mutability: None,
                    ident,
                    subpat: None,
                    ..
                }) => {
                    locals.bind_ref(ident.clone());
                    quote! { #ident : &_ }
                }
                pat => {
                    pattern_bind(pat, locals);
                    quote! { &#pat }
                }
            };
            let retty = &clos.output;
            let clos = encode_term_(&clos.body, locals)?;
            locals.close();
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::mapping_from_fn(
                    #[creusot::no_translate] #[creusot::logic_closure] |#input| #retty #clos)
            })
        }
        RT::__Nonexhaustive => todo!(),
    }
}

fn encode_trigger_(
    mut trigger: &[Trigger],
    mut ts: TokenStream,
    locals: &mut Locals,
) -> Result<TokenStream, EncodeError> {
    while let [rest @ .., last] = trigger {
        trigger = rest;
        let trigs =
            last.terms.iter().map(|t| encode_term_(t, locals)).collect::<Result<Vec<_>, _>>()?;
        ts = quote!(::creusot_contracts::__stubs::trigger((#(#trigs,)*), #ts))
    }
    Ok(ts)
}

pub fn encode_block(block: &TBlock) -> TokenStream {
    encode_block_(block, &mut Locals::new())
}

fn encode_block_(block: &TBlock, locals: &mut Locals) -> TokenStream {
    // If there are errors during encode_stmt_, still emit the braces
    // to allow the parser to skip over the body and discover more errors.
    let mut tokens = TokenStream::new();
    locals.open();
    block.brace_token.surround(&mut tokens, |tokens| {
        block.stmts.iter().for_each(|stmt| {
            encode_stmt_(stmt, locals).unwrap_or_else(|e| e.into_tokens()).to_tokens(tokens)
        })
    });
    locals.close();
    tokens
}

pub fn encode_stmt(stmt: &TermStmt) -> Result<TokenStream, EncodeError> {
    encode_stmt_(stmt, &mut Locals::new())
}

fn encode_stmt_(stmt: &TermStmt, locals: &mut Locals) -> Result<TokenStream, EncodeError> {
    match stmt {
        TermStmt::Local(TLocal { let_token, pat, init, semi_token }) => {
            if let Some((eq_token, init)) = init {
                let init = encode_term_(init, locals)?;
                pattern_bind(pat, locals);
                Ok(quote! { #let_token #pat #eq_token #init #semi_token })
            } else {
                Err(EncodeError::LocalLetNoInit(pat.span()))
            }
        }
        TermStmt::Expr(e) => encode_term_(e, locals),
        TermStmt::Semi(t, s) => {
            let term = encode_term_(t, locals)?;
            Ok(quote! { #term #s })
        }
        TermStmt::Item(i) => Ok(quote! { #i }),
        TermStmt::Empty(s) => Ok(quote! { #s }),
    }
}

impl<'a> Visit<'a> for &'a mut Locals {
    fn visit_pat(&mut self, pat: &'a Pat) {
        match pat {
            Pat::Path(path) if let Some(ident) = path.path.get_ident() => self.bind_raw(ident),
            Pat::Ident(ident) => self.bind_raw(&ident.ident),
            _ => visit_pat(self, pat),
        }
    }
}

/// `bind_raw` on every variable in `pat`
fn pattern_bind<'a>(pat: &'a Pat, mut locals: &'a mut Locals) {
    locals.visit_pat(pat)
}

fn encode_arm_(arm: &TermArm, locals: &mut Locals) -> Result<TokenStream, EncodeError> {
    if arm.guard.is_some() {
        return Err(EncodeError::Unsupported(arm.span(), "match guard".to_string()));
    }
    let comma = &arm.comma;
    let pat = &arm.pat;
    locals.open();
    pattern_bind(&pat, locals);
    let body = encode_term_(&arm.body, locals)?;
    locals.close();
    Ok(quote! { #pat => #body #comma })
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
