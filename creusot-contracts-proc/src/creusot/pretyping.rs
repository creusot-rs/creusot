//! Pre-parse pearlite.
//!
//! Some macros accept pearlite rather than Rust. This module converts the
//! latter to the former.
//!
//! For example, `1 + 2` becomes `creusot_contracts::logic::AddLogic::add(Int::new(1), Int::new(2))`.

use pearlite_syn::{Term, term::*};
use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use quote::{ToTokens, quote_spanned};
use std::collections::HashSet;
use syn::{
    Ident, Lit, Pat, PatIdent, PatType, Path, UnOp, parse_quote_spanned,
    spanned::Spanned,
    visit::{Visit, visit_pat},
};

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

fn add_use(toks: TokenStream, span: Span) -> TokenStream {
    quote_spanned! { span =>
        {
            #[allow(unused)]
            use ::creusot_contracts::__stubs::{IndexLogicStub as _, ViewStub as _};
            #toks
        }
    }
}

pub fn encode_term(term: &Term) -> TokenStream {
    match encode_term_(term, &mut Locals::new()) {
        Ok(r) => add_use(r.toks(), term.span()),
        Err(e) => e.into_tokens(),
    }
}

// Pearlite terms can refer to function parameters of unsized types. However, pearlite terms often
// appear in closures, which can only capture sized values. Hence, we wrap any reference to a variable x
// with (*&x). In order to support partial captures, we try to do this wrapping at the place level
// (i.e., if the user writes x.a, then we emit (&* x.a)). This is the purpose of this struct: if `encode_term_`
// returns deref_bor: true, then we have to wrap the result in &* at a higher level.
struct EncodingResult {
    toks: TokenStream,
    deref_bor: bool,
}

impl EncodingResult {
    fn toks(self) -> TokenStream {
        let EncodingResult { toks, deref_bor } = self;
        if deref_bor {
            quote_spanned! { toks.span() => (*& #toks) }
        } else {
            toks
        }
    }
}

impl From<TokenStream> for EncodingResult {
    fn from(toks: TokenStream) -> EncodingResult {
        EncodingResult { toks, deref_bor: false }
    }
}

// TODO: Rewrite this as a source to source transform and *then* call ToTokens on the result
fn encode_term_(term: &Term, locals: &mut Locals) -> Result<EncodingResult, EncodeError> {
    let sp = term.span();
    match term {
        // It's unclear what to do with macros. Either we translate the parameters, but then
        // it's impossible to handle proc macros whose parameters is not valid pearlite syntax,
        // or we don't translate parameters, but then we let the user write non-pearlite code
        // in pearlite...
        Term::Macro(term) => {
            let mut term = term.clone();
            let path: Path = if term.mac.path.is_ident("proof_assert") {
                parse_quote_spanned! { term.mac.path.span() => ::creusot_contracts::macros::proof_assert }
            } else if term.mac.path.is_ident("pearlite") {
                parse_quote_spanned! { term.mac.path.span() => ::creusot_contracts::macros::pearlite }
            } else if term.mac.path.is_ident("seq") {
                parse_quote_spanned! { term.mac.path.span() => ::creusot_contracts::logic::seq::seq }
            } else {
                return Err(EncodeError::Unsupported(
                        sp,
                        "macros other than `pearlite!` or `proof_assert!` or `seq!` are unsupported in pearlite code".into(),
                    ));
            };
            term.mac.path = path;
            Ok(term.to_token_stream().into())
        }
        Term::Array(_) => Err(EncodeError::Unsupported(sp, "Array".into())),
        Term::Binary(TermBinary { left, op, right }) => {
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
                    Term::Paren(TermParen { expr, .. }) => expr,
                    _ => left,
                };
                right = match &**right {
                    Term::Paren(TermParen { expr, .. }) => expr,
                    _ => right,
                };
            }

            let left = encode_term_(left, locals)?.toks();
            let right = encode_term_(right, locals)?.toks();
            match op {
                Eq(_) => {
                    Ok(quote_spanned! {sp=> ::creusot_contracts::__stubs::equal(#left, #right) }.into())
                }
                Ne(_) => {
                    Ok(quote_spanned! {sp=> ::creusot_contracts::__stubs::neq(#left, #right) }.into())
                }
                Lt(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::lt_log(#left, #right) }.into(),
                ),
                Le(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::le_log(#left, #right) }.into(),
                ),
                Ge(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::ge_log(#left, #right) }.into(),
                ),
                Gt(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::OrdLogic::gt_log(#left, #right) }.into(),
                ),
                Add(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::AddLogic::add(#left, #right) }.into(),
                ),
                Sub(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::SubLogic::sub(#left, #right) }.into(),
                ),
                Mul(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::MulLogic::mul(#left, #right) }.into(),
                ),
                Div(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::DivLogic::div(#left, #right) }.into(),
                ),
                Rem(_) => Ok(
                    quote_spanned! {sp=> ::creusot_contracts::logic::ops::RemLogic::rem(#left, #right) }.into(),
                ),
                _ => Ok(quote_spanned! {sp=> #left #op #right }.into()),
            }
        }
        Term::Block(TermBlock { block, .. }) => Ok(encode_block_(block, locals).into()),
        Term::Call(TermCall { func, args, .. }) => {
            let args: Vec<_> = args
                .into_iter()
                .map(|t| Ok(encode_term_(t, locals)?.toks()))
                .collect::<Result<_, _>>()?;
            if let Term::Path(p) = &**func {
                if p.inner.path.is_ident("old") {
                    return Ok(
                        quote_spanned! {sp=> (*::creusot_contracts::__stubs::old( #(#args),* )) }
                            .into(),
                    );
                }
                // Don't wrap function calls in `*&`.
                return Ok(quote_spanned! {sp=> #func (#(#args),*)}.into());
            } else {
                Err(EncodeError::Unsupported(
                    sp,
                    "(expr)() where (expr) is not an identifier".to_string(),
                ))
            }
        }
        Term::Cast(TermCast { expr, as_token, ty }) => {
            let expr_token = encode_term_(expr, locals)?.toks();
            Ok(quote_spanned! {sp=> #expr_token #as_token  #ty}.into())
        }
        Term::Field(TermField { base, member, .. }) => {
            let EncodingResult { toks, deref_bor } = encode_term_(base, locals)?;
            Ok(EncodingResult { toks: quote_spanned!(sp => #toks . #member), deref_bor })
        }
        Term::Group(TermGroup { expr, .. }) => {
            let term = encode_term_(expr, locals)?.toks();
            let mut res = TokenStream::new();
            res.extend_one(TokenTree::Group(Group::new(Delimiter::None, term)));
            Ok(res.into())
        }
        Term::If(TermIf { cond, then_branch, else_branch, .. }) => {
            let cond = if let Term::Paren(TermParen { expr, .. }) = &**cond
                && matches!(&**expr, Term::Quant(_))
            {
                &**expr
            } else {
                cond
            };
            let cond = encode_term_(cond, locals)?.toks();
            let then_branch: Vec<_> = then_branch
                .stmts
                .iter()
                .map(|s| encode_stmt_(s, locals))
                .collect::<Result<_, _>>()?;
            let else_branch = match else_branch {
                Some((_, t)) => {
                    let term = encode_term_(t, locals)?.toks();
                    Some(quote_spanned! {sp=> else #term })
                }
                None => None,
            };
            Ok(quote_spanned! {sp=> if #cond { #(#then_branch)* } #else_branch }.into())
        }
        Term::Index(TermIndex { expr, index, .. }) => {
            let expr =
                if let Term::Paren(TermParen { expr, .. }) = &**expr { &**expr } else { expr };

            let expr = encode_term_(expr, locals)?.toks();
            let index = encode_term_(index, locals)?.toks();

            Ok(quote_spanned! {sp=> (#expr).__creusot_index_logic_stub(#index)}.into())
        }
        Term::Let(_) => Err(EncodeError::Unsupported(term.span(), "Let".into())),
        Term::Lit(TermLit { lit: lit @ Lit::Int(int) }) if int.suffix() == "" => {
            // FIXME: allow unbounded integers
            Ok(quote_spanned! {sp=> ::creusot_contracts::model::View::view(#lit as i128) }.into())
        }
        Term::Lit(TermLit { lit: Lit::Int(int) }) if int.suffix() == "int" => {
            let lit = syn::LitInt::new(int.base10_digits(), int.span());
            Ok(quote_spanned! {sp=> ::creusot_contracts::model::View::view(#lit as i128) }.into())
        }
        Term::Lit(TermLit { lit }) => Ok(quote_spanned! {sp=> #lit }.into()),
        Term::Match(TermMatch { expr, arms, .. }) => {
            let arms: Vec<_> =
                arms.iter().map(|a| encode_arm_(a, locals)).collect::<Result<_, _>>()?;
            let expr = encode_term_(expr, locals)?.toks();
            Ok(quote_spanned! {sp=> match #expr { #(#arms)* } }.into())
        }
        Term::MethodCall(TermMethodCall { receiver, method, turbofish, args, .. }) => {
            let receiver = encode_term_(receiver, locals)?.toks();
            let args: Vec<_> = args
                .into_iter()
                .map(|t| Ok(encode_term_(t, locals)?.toks()))
                .collect::<Result<_, _>>()?;
            Ok(quote_spanned! {sp=> #receiver . #method #turbofish ( #(#args),*) }.into())
        }
        Term::Paren(TermParen { paren_token, expr }) => {
            let mut tokens = TokenStream::new();
            let EncodingResult { toks, deref_bor } = encode_term_(expr, locals)?;
            paren_token.surround(&mut tokens, |tokens| {
                tokens.extend(toks);
            });
            Ok(EncodingResult { toks: tokens, deref_bor })
        }
        Term::Path(path) if let Some(ident) = path.inner.path.get_ident() => {
            Ok(if locals.is_ref_bound(ident) {
                quote_spanned! { sp=> (*#ident) }.into()
            } else {
                EncodingResult { toks: quote_spanned! { sp=> #ident }, deref_bor: true }
            })
        }
        Term::Path(path) => Ok(quote_spanned! { sp=> #path }.into()),
        Term::Range(_) => Err(EncodeError::Unsupported(term.span(), "Range".into())),
        Term::Reference(TermReference { mutability, expr, .. }) => {
            let term = encode_term_(expr, locals)?.toks();
            Ok(quote_spanned! {sp=>
                & #mutability #term
            }
            .into())
        }
        Term::Repeat(_) => Err(EncodeError::Unsupported(term.span(), "Repeat".into())),
        Term::Struct(TermStruct { path, fields, rest, brace_token, dot2_token }) => {
            let mut ts = TokenStream::new();
            path.to_tokens(&mut ts);

            let mut inner = TokenStream::new();

            for p in fields.pairs() {
                let (tv, punc) = p.into_tuple();

                tv.member.to_tokens(&mut inner);
                if let Some(colon) = tv.colon_token {
                    colon.to_tokens(&mut inner);
                    inner.extend(encode_term_(&tv.expr, locals)?.toks())
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

            Ok(ts.into())
        }
        Term::Tuple(TermTuple { elems, .. }) => {
            if elems.is_empty() {
                return Ok(quote_spanned! {sp=> () }.into());
            }
            let elems: Vec<_> = elems
                .into_iter()
                .map(|t| Ok(encode_term_(t, locals)?.toks()))
                .collect::<Result<_, _>>()?;
            Ok(quote_spanned! {sp=> (#(#elems),*,) }.into())
        }
        Term::Type(ty) => Ok(quote_spanned! {sp=> #ty }.into()),
        Term::Unary(TermUnary { op, expr }) => match op {
            UnOp::Neg(_) => {
                let term = encode_term_(expr, locals)?.toks();
                Ok(quote_spanned! {sp=> ::creusot_contracts::logic::ops::NegLogic::neg(#term) }
                    .into())
            }
            UnOp::Deref(_) => {
                let EncodingResult { toks, deref_bor } = encode_term_(expr, locals)?;
                Ok(EncodingResult { toks: quote_spanned! {sp=> #op #toks }, deref_bor })
            }
            _ => {
                let term = encode_term_(expr, locals)?.toks();
                Ok(quote_spanned! {sp=> #op #term }.into())
            }
        },
        Term::Final(TermFinal { term, .. }) => {
            let term = encode_term_(term, locals)?.toks();
            Ok(quote_spanned! {sp=>
                (*::creusot_contracts::logic::ops::Fin::fin(#term))
            }
            .into())
        }
        Term::View(TermView { term, .. }) => {
            let term = match &**term {
                Term::Paren(TermParen { expr, .. }) => expr,
                _ => term,
            };
            let term = encode_term_(term, locals)?.toks();
            Ok(quote_spanned! {sp=> ((#term).__creusot_view_stub()) }.into())
        }
        Term::LogEq(TermLogEq { lhs, rhs, .. }) => {
            let lhs = encode_term_(lhs, locals)?.toks();
            let rhs = encode_term_(rhs, locals)?.toks();
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::equal(#lhs, #rhs)
            }
            .into())
        }
        Term::Impl(TermImpl { hyp, cons, .. }) => {
            let hyp = match &**hyp {
                Term::Paren(TermParen { expr, .. }) => match &**expr {
                    Term::Quant(_) => expr,
                    _ => hyp,
                },
                _ => hyp,
            };
            let hyp = encode_term_(hyp, locals)?.toks();
            let cons = encode_term_(cons, locals)?.toks();
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::implication(#hyp, #cons)
            }
            .into())
        }
        Term::Quant(TermQuant { quant_token, args, trigger, term, .. }) => {
            locals.open();
            let args_ref = args
                .iter()
                .map(|qa @ QuantArg { ident, ty }| {
                    locals.bind_ref(ident.clone());
                    match ty {
                        None => quote_spanned! {qa.span()=> #ident: &_ },
                        Some((_, ty)) => quote_spanned! {qa.span()=> #ident: &#ty },
                    }
                })
                .collect::<Vec<_>>();
            let mut ts = encode_term_(term, locals)?.toks();
            ts = encode_trigger_(trigger, ts, locals)?;
            locals.close();
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::#quant_token(
                    #[creusot::no_translate]
                    #[creusot::logic_closure]
                    |#(#args_ref,)*| { #ts }
                )
            }
            .into())
        }
        Term::Dead(_) => Ok(quote_spanned! {sp=> (*::creusot_contracts::__stubs::dead()) }.into()),
        Term::Pearlite(term) => Ok(quote_spanned! {sp=> #term }.into()),
        Term::Closure(clos) => {
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
                    quote_spanned! {sp=> #(#attrs)* #ident : &#ty }
                }
                // |pat: ty|
                Pat::Type(PatType { attrs, pat, ty, .. }) => {
                    pattern_bind(pat, locals);
                    quote_spanned! {sp=> #(#attrs)* &#pat : &#ty }
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
                    quote_spanned! {sp=> #ident : &_ }
                }
                pat => {
                    pattern_bind(pat, locals);
                    quote_spanned! {sp=> &#pat }
                }
            };
            let retty = &clos.output;
            let clos = encode_term_(&clos.body, locals)?.toks();
            locals.close();
            Ok(quote_spanned! {sp=>
                ::creusot_contracts::__stubs::mapping_from_fn(
                    #[creusot::no_translate] #[creusot::logic_closure] |#input| #retty #clos)
            }
            .into())
        }
        Term::__Nonexhaustive => todo!(),
    }
}

fn encode_trigger_(
    mut trigger: &[Trigger],
    mut ts: TokenStream,
    locals: &mut Locals,
) -> Result<TokenStream, EncodeError> {
    while let [rest @ .., last] = trigger {
        trigger = rest;
        let trigs = last
            .terms
            .iter()
            .map(|t| Ok(encode_term_(t, locals)?.toks()))
            .collect::<Result<Vec<_>, _>>()?;
        let span = last.span();
        ts = quote_spanned!(span=>::creusot_contracts::__stubs::trigger((#(#trigs,)*), #ts))
    }
    Ok(ts)
}

fn encode_block_(block: &TBlock, locals: &mut Locals) -> TokenStream {
    // If there are errors during encode_stmts_, still emit the braces
    // to allow the parser to skip over the body and discover more errors.
    let mut tokens = TokenStream::new();
    locals.open();
    block
        .brace_token
        .surround(&mut tokens, |tokens| encode_stmts_(&block.stmts, locals).to_tokens(tokens));
    locals.close();
    tokens
}

pub fn encode_block(block: &TBlock) -> TokenStream {
    encode_stmts(&block.stmts, block.span())
}

fn encode_stmts_(stmts: &[TermStmt], locals: &mut Locals) -> TokenStream {
    let mut tokens = TokenStream::new();
    for stmt in stmts.iter() {
        encode_stmt_(stmt, locals).unwrap_or_else(|e| e.into_tokens()).to_tokens(&mut tokens)
    }
    tokens
}

pub fn encode_stmts(stmts: &[TermStmt], span: Span) -> TokenStream {
    let toks = encode_stmts_(stmts, &mut Locals::new());
    add_use(toks, span)
}

fn encode_stmt_(stmt: &TermStmt, locals: &mut Locals) -> Result<TokenStream, EncodeError> {
    match stmt {
        TermStmt::Local(TLocal { let_token, pat, init, semi_token }) => {
            if let Some((eq_token, init)) = init {
                let init = encode_term_(init, locals)?.toks();
                pattern_bind(pat, locals);
                Ok(quote_spanned! {stmt.span() => #let_token #pat #eq_token #init #semi_token })
            } else {
                Err(EncodeError::LocalLetNoInit(pat.span()))
            }
        }
        TermStmt::Expr(e) => Ok(encode_term_(e, locals)?.toks()),
        TermStmt::Semi(t, s) => {
            let term = encode_term_(t, locals)?.toks();
            Ok(quote_spanned! {stmt.span() => #term #s })
        }
        TermStmt::Item(i) => Ok(quote_spanned! {stmt.span() => #i }),
        TermStmt::Empty(s) => Ok(quote_spanned! {stmt.span() => #s }),
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
    let body = encode_term_(&arm.body, locals)?.toks();
    locals.close();
    Ok(quote_spanned! {arm.span()=> #pat => #body #comma })
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
