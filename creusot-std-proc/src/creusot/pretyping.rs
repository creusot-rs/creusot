//! Pre-parse pearlite.
//!
//! Some macros accept pearlite rather than Rust. This module converts the
//! latter to the former.
//!
//! For example, `1 + 2` becomes `creusot_std::logic::AddLogic::add_logic(Int::new(1), Int::new(2))`.

use pearlite_syn::{Term, term::*};
use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use quote::{ToTokens, quote, quote_spanned};
use std::collections::HashSet;
use syn::{
    Ident, Lit, LitInt, Pat, PatIdent, PatType, RangeLimits, UnOp,
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

struct PatEncoder<'a> {
    locals: &'a mut Locals,
    has_literal_int: bool, // #1827
}

impl<'a> PatEncoder<'a> {
    fn new(locals: &'a mut Locals) -> Self {
        Self { locals, has_literal_int: false }
    }
}

fn add_use(toks: TokenStream, span: Span) -> TokenStream {
    let use_ = quote_spanned! { Span::mixed_site() =>
        #[allow(unused)]
        use ::creusot_std::__stubs::{IndexLogicStub as _, ViewStub as _};
    };

    quote_spanned! { span =>
        {
            #use_
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

pub fn encode_term_with_triggers(term: &TermWithTriggers) -> TokenStream {
    match encode_term_with_triggers_(term, &mut Locals::new()) {
        Ok(r) => add_use(r, term.span()),
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
            quote_spanned! { span_before(toks.span()) => *& #toks }
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

fn span_before(sp: Span) -> Span {
    if proc_macro::is_available() { sp.located_at(sp.unwrap().start().into()) } else { sp }
}

fn span_after(sp: Span) -> Span {
    if proc_macro::is_available() { sp.located_at(sp.unwrap().end().into()) } else { sp }
}

fn span_join(a: Span, b: Span) -> Span {
    a.join(b).unwrap_or(a)
}

// TODO: Rewrite this as a source to source transform and *then* call ToTokens on the result
fn encode_term_(term: &Term, locals: &mut Locals) -> Result<EncodingResult, EncodeError> {
    let sp = term.span();
    let deref = quote_spanned! { span_before(sp) => * };
    match term {
        Term::Array(_) => Err(EncodeError::Unsupported(sp, "Array".into())),
        Term::Binary(TermBinary { left, op, right }) => {
            let mut left = left;
            let mut right = right;

            use syn::BinOp::*;
            if matches!(
                op,
                Eq(_)
                    | Ne(_)
                    | Lt(_)
                    | Le(_)
                    | Ge(_)
                    | Gt(_)
                    | Add(_)
                    | Sub(_)
                    | Mul(_)
                    | Div(_)
                    | Rem(_)
                    | BitAnd(_)
                    | BitOr(_)
                    | BitXor(_)
                    | Shl(_)
                    | Shr(_)
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

            let stream = match op {
                Eq(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::__stubs:: },
                    quote_spanned! { op.span() => equal },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Ne(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::__stubs:: },
                    quote_spanned! { op.span() => neq },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Lt(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::PartialOrdLogic:: },
                    quote_spanned! { op.span() => lt_log },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Le(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::PartialOrdLogic:: },
                    quote_spanned! { op.span() => le_log },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Gt(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::PartialOrdLogic:: },
                    quote_spanned! { op.span() => gt_log },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Ge(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::PartialOrdLogic:: },
                    quote_spanned! { op.span() => ge_log },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Add(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::AddLogic:: },
                    quote_spanned! { op.span() => add_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Sub(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::SubLogic:: },
                    quote_spanned! { op.span() => sub_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Mul(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::MulLogic:: },
                    quote_spanned! { op.span() => mul_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Div(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::DivLogic:: },
                    quote_spanned! { op.span() => div_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Rem(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::RemLogic:: },
                    quote_spanned! { op.span() => rem_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                BitAnd(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::BitAndLogic:: },
                    quote_spanned! { op.span() => bitand_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                BitOr(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::BitOrLogic:: },
                    quote_spanned! { op.span() => bitor_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                BitXor(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::BitXorLogic:: },
                    quote_spanned! { op.span() => bitxor_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Shl(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::ShlLogic:: },
                    quote_spanned! { op.span() => shl_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                Shr(_) => TokenStream::from_iter([
                    quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::ShrLogic:: },
                    quote_spanned! { op.span() => shr_logic },
                    quote_spanned! { sp => (#left, #right) },
                ]),
                _ => quote_spanned! { sp => (#left) #op (#right) },
            };
            Ok(stream.into())
        }
        Term::Block(block) => Ok(encode_block_(block, locals).into()),
        Term::Call(TermCall { func, args, .. }) => {
            let args: Vec<_> = args
                .into_iter()
                .map(|t| Ok(encode_term_(t, locals)?.toks()))
                .collect::<Result<_, _>>()?;
            if let Term::Path(p) = &**func {
                let path = &p.inner.path;
                let stream = if path.is_ident("old") {
                    TokenStream::from_iter([
                        quote_spanned! { span_before(path.span()) => #deref ::creusot_std::__stubs:: },
                        quote_spanned! { path.span() => old },
                        quote_spanned! { sp => ( #(#args,)* ) },
                    ])
                } else {
                    // Don't wrap function calls in `*&`.
                    quote_spanned! { sp => #func (#(#args,)*) }
                };
                Ok(stream.into())
            } else {
                Err(EncodeError::Unsupported(
                    sp,
                    "(expr)() where (expr) is not an identifier".to_string(),
                ))
            }
        }
        Term::Cast(TermCast { expr, as_token, ty }) => {
            let expr_token = encode_term_(expr, locals)?.toks();
            Ok(quote! { #expr_token #as_token #ty }.into())
        }
        Term::Field(TermField { base, member, dot_token }) => {
            let EncodingResult { toks, deref_bor } = encode_term_(base, locals)?;
            Ok(EncodingResult {
                toks: quote_spanned! { toks.span() => (#toks) #dot_token #member },
                deref_bor,
            })
        }
        Term::Group(TermGroup { expr, .. }) => {
            let term = encode_term_(expr, locals)?.toks();

            Ok(TokenStream::from_iter([TokenTree::Group(Group::new(Delimiter::None, term))]).into())
        }
        Term::If(TermIf { cond, then_branch, else_branch, if_token }) => {
            let cond = if let Term::Paren(TermParen { expr, .. }) = &**cond
                && matches!(&**expr, Term::Quant(_))
            {
                &**expr
            } else {
                cond
            };
            let cond = encode_term_(cond, locals)?.toks();
            let then_span = then_branch.span();
            let then_branch: Vec<_> = then_branch
                .stmts
                .iter()
                .map(|s| encode_stmt_(s, locals))
                .collect::<Result<_, _>>()?;
            let else_branch = match else_branch {
                Some((else_token, t)) => {
                    let term = encode_term_(t, locals)?.toks();
                    Some(quote! { #else_token #term })
                }
                None => None,
            };
            Ok(quote_spanned! { then_span=> #if_token #cond { #(#then_branch)* } #else_branch }
                .into())
        }
        Term::Index(TermIndex { expr, index, bracket_token }) => {
            let expr =
                if let Term::Paren(TermParen { expr, .. }) = &**expr { &**expr } else { expr };

            let expr = encode_term_(expr, locals)?.toks();
            let index = encode_term_(index, locals)?.toks();

            let stream = TokenStream::from_iter([
                quote_spanned! { expr.span() => (#expr) },
                // making the span any larger makes it include the expr/index spans which messes
                // with rust-analyzer span tracking
                quote_spanned! { bracket_token.span.open() => .__creusot_index_logic_stub },
                quote_spanned! { bracket_token.span => (#index) },
            ]);
            Ok(stream.into())
        }
        Term::Let(_) => Err(EncodeError::Unsupported(term.span(), "Let".into())),
        Term::Lit(TermLit { lit: lit @ Lit::Int(int) })
            if int.suffix() == "" || int.suffix() == "int" =>
        {
            let tmp;
            let int = if int.suffix() == "int" {
                tmp = LitInt::new(int.base10_digits(), int.span());
                &tmp
            } else {
                int
            };

            // FIXME: allow unbounded integers
            let inner = quote_spanned! { span_after(int.span()) => #int as i128 };
            let stream = TokenStream::from_iter([
                quote_spanned! { span_before(int.span()) => ::creusot_std::model::View::view },
                quote_spanned! { int.span() => (#inner) },
            ]);
            Ok(stream.into())
        }
        Term::Lit(TermLit { lit }) => Ok(quote! { #lit }.into()),
        Term::Match(TermMatch { expr, arms, match_token, brace_token }) => {
            let arms: Vec<_> =
                arms.iter().map(|a| encode_arm_(a, locals)).collect::<Result<_, _>>()?;
            let expr = encode_term_(expr, locals)?.toks();
            Ok(quote_spanned! { brace_token.span => #match_token #expr { #(#arms)* } }.into())
        }
        Term::MethodCall(TermMethodCall {
            receiver,
            method,
            turbofish,
            args,
            dot_token,
            paren_token,
        }) => {
            let receiver = encode_term_(receiver, locals)?.toks();
            let args_span = term.span();
            let args: Vec<_> = args
                .into_iter()
                .map(|t| Ok(encode_term_(t, locals)?.toks()))
                .collect::<Result<_, _>>()?;
            let stream = TokenStream::from_iter([
                quote_spanned! { paren_token.span => (#receiver) },
                quote_spanned! { args_span => #dot_token #method #turbofish (#(#args,)*) },
            ]);
            Ok(stream.into())
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
                quote! { #deref #ident }.into()
            } else {
                EncodingResult { toks: quote! { #ident }, deref_bor: true }
            })
        }
        Term::Path(path) => Ok(quote! { #path }.into()),
        // Special case to desugar x..=y to RangeInclusive::new_log (instead of new, which is a program function)
        Term::Range(TermRange {
            from: Some(from),
            limits: RangeLimits::Closed(limits),
            to: Some(to),
        }) => {
            let from = encode_term_(from, locals)?.toks();
            let to = encode_term_(to, locals)?.toks();
            let stream = TokenStream::from_iter([
                quote_spanned! { span_before(sp) =>
                    <::core::ops::RangeInclusive<_> as ::creusot_std::std::ops::RangeInclusiveExt<_>>::
                },
                quote_spanned! { limits.span() => new_log },
                quote_spanned! { sp => (#from, #to) },
            ]);
            Ok(stream.into())
        }
        Term::Range(TermRange { from, limits, to }) => {
            let from = match from {
                None => TokenStream::new(),
                Some(t) => encode_term_(t, locals)?.toks(),
            };
            let to = match to {
                None => TokenStream::new(),
                Some(t) => encode_term_(t, locals)?.toks(),
            };
            Ok(quote! { #from #limits #to }.into())
        }
        Term::Reference(TermReference { mutability, expr, and_token }) => {
            let term = encode_term_(expr, locals)?.toks();
            Ok(quote! { #and_token #mutability #term }.into())
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
            let elems: Vec<_> = elems
                .into_iter()
                .map(|t| Ok(encode_term_(t, locals)?.toks()))
                .collect::<Result<_, _>>()?;
            Ok(quote_spanned! { sp => (#(#elems,)*) }.into())
        }
        Term::Type(ty) => Ok(quote! { #ty }.into()),
        Term::Unary(TermUnary { op, expr }) => {
            let mut expr = expr;
            if matches!(op, UnOp::Neg(_) | UnOp::Not(_) | UnOp::Deref(_)) {
                expr = match &**expr {
                    Term::Paren(TermParen { expr, .. }) => expr,
                    _ => expr,
                };
            }

            match op {
                UnOp::Neg(_) => {
                    let expr = encode_term_(expr, locals)?.toks();
                    let stream = TokenStream::from_iter([
                        quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::NegLogic:: },
                        quote_spanned! { op.span() => neg_logic },
                        quote_spanned! { sp => (#expr) },
                    ]);
                    Ok(stream.into())
                }
                UnOp::Not(_) => {
                    let expr = encode_term_(expr, locals)?.toks();
                    let stream = TokenStream::from_iter([
                        quote_spanned! { span_before(op.span()) => ::creusot_std::logic::ops::NotLogic:: },
                        quote_spanned! { op.span() => not_logic },
                        quote_spanned! { sp => (#expr) },
                    ]);
                    Ok(stream.into())
                }
                UnOp::Deref(_) => {
                    let EncodingResult { toks, deref_bor } = encode_term_(expr, locals)?;
                    Ok(EncodingResult {
                        toks: quote_spanned! { expr.span() => #op (#toks) },
                        deref_bor,
                    })
                }
                _ => {
                    let expr = encode_term_(expr, locals)?.toks();
                    Ok(quote_spanned! { expr.span() => #op (#expr) }.into())
                }
            }
        }
        Term::Final(TermFinal { term, final_token }) => {
            let term = encode_term_(term, locals)?.toks();
            let stream = TokenStream::from_iter([
                quote_spanned! { span_before(final_token.span()) => #deref ::creusot_std::logic::ops::Fin:: },
                quote_spanned! { final_token.span() => fin },
                quote_spanned! { sp => (#term) },
            ]);
            Ok(stream.into())
        }
        Term::View(TermView { term, at_token }) => {
            let term = match &**term {
                Term::Paren(TermParen { expr, .. }) => expr,
                _ => term,
            };
            let term = encode_term_(term, locals)?.toks();
            let stream = TokenStream::from_iter([
                quote_spanned! { sp => (#term) },
                quote_spanned! { span_before(at_token.span()) => . },
                quote_spanned! { at_token.span() => __creusot_view_stub },
                quote_spanned! { span_after(at_token.span()) => () },
            ]);
            Ok(stream.into())
        }
        Term::Impl(TermImpl { hyp, cons, eqeq_token, gt_token }) => {
            let hyp = match &**hyp {
                Term::Paren(TermParen { expr, .. }) => match &**expr {
                    Term::Quant(_) => expr,
                    _ => hyp,
                },
                _ => hyp,
            };
            let hyp = encode_term_(hyp, locals)?.toks();
            let cons = encode_term_(cons, locals)?.toks();

            let implication_sp = span_join(eqeq_token.span(), gt_token.span());
            let stream = TokenStream::from_iter([
                quote_spanned! { span_before(implication_sp) => ::creusot_std::__stubs:: },
                quote_spanned! { implication_sp => implication },
                quote_spanned! { sp => (#hyp, #cons) },
            ]);
            Ok(stream.into())
        }
        Term::Quant(TermQuant { quant_token, args, term, lt_token, gt_token }) => {
            locals.open();
            let args_ref = args
                .iter()
                .map(|qa @ QuantArg { ident, ty }| {
                    locals.bind_ref(ident.clone());
                    match ty {
                        None => quote_spanned! { span_after(qa.span()) => #ident: &_ },
                        Some((_, ty)) => quote_spanned! { span_after(qa.span()) => #ident: &#ty },
                    }
                })
                .collect::<Vec<_>>();
            let ts = encode_term_with_triggers_(term, locals)?;
            locals.close();
            let open_token = quote_spanned! { lt_token.span() => | };
            let close_token = quote_spanned! { gt_token.span() => | };
            Ok(quote_spanned! { span_before(sp) =>
                ::creusot_std::__stubs::#quant_token(
                    #[creusot::no_translate]
                    #[creusot::logic_closure]
                    #open_token #(#args_ref,)* #close_token #ts
                )
            }
            .into())
        }
        Term::Dead(_) => {
            let stream = TokenStream::from_iter([
                quote_spanned! { span_before(sp) => #deref ::creusot_std::__stubs::},
                quote_spanned! { sp => dead },
                quote_spanned! { span_after(sp) => () },
            ]);
            Ok(stream.into())
        }
        Term::Pearlite(TermPearlite { block, .. }) => {
            let term = encode_block_(block, locals);
            let stream =
                quote_spanned! { span_before(term.span()) => #[allow(unused_braces)] #term };
            Ok(TokenStream::from_iter([TokenTree::Group(Group::new(Delimiter::None, stream))])
                .into())
        }
        Term::ProofAssert(TermProofAssert { block, .. }) => {
            let assert_body = encode_block_(block, locals);
            Ok(quote_spanned! { span_before(sp) =>
                {
                    #[allow(let_underscore_drop)]
                    let _ =
                        #[creusot::no_translate]
                        #[creusot::spec]
                        #[creusot::spec::assert]
                        || -> bool #assert_body;
                }
            }
            .into())
        }
        Term::Seq(TermSeq { terms, seq_token, bang_token, .. }) => {
            let seq_token = span_join(seq_token.span(), bang_token.span());
            if terms.is_empty() {
                let stream = TokenStream::from_iter([
                    quote_spanned! { span_before(sp) => ::creusot_std::logic::seq::Seq:: },
                    quote_spanned! { seq_token.span() => empty },
                    quote_spanned! { span_after(sp) => () },
                ]);
                return Ok(stream.into());
            }

            let terms: Vec<_> = terms
                .into_iter()
                .map(|t| Ok(encode_term_(t, locals)?.toks()))
                .collect::<Result<_, _>>()?;
            let stream = TokenStream::from_iter([
                quote_spanned! { span_before(sp) => ::creusot_std::__stubs:: },
                quote_spanned! { seq_token.span() => seq_literal },
                quote_spanned! { span_after(sp) => (&[#(#terms,)*]) },
            ]);
            Ok(stream.into())
        }
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
                    colon_token,
                }) => {
                    locals.bind_ref(ident.clone());
                    quote! { #(#attrs)* #ident #colon_token &#ty }
                }
                // |pat: ty|
                Pat::Type(PatType { attrs, pat, ty, colon_token }) => {
                    pattern_bind(pat, locals, term.span())?;
                    quote! { #(#attrs)* &#pat #colon_token &#ty }
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
                    quote_spanned! { span_after(ident.span()) => #ident : &_ }
                }
                pat => {
                    pattern_bind(pat, locals, term.span())?;
                    quote_spanned! { span_before(pat.span()) => &#pat }
                }
            };
            let retty = &clos.output;
            let clos = encode_term_(&clos.body, locals)?.toks();
            locals.close();
            Ok(quote_spanned! { span_before(sp)=>
                ::creusot_std::__stubs::mapping_from_fn(
                    #[creusot::no_translate] #[creusot::logic_closure] |#input| #retty #clos)
            }
            .into())
        }
        Term::Mode(_) => Ok(quote_spanned! {sp=>
            ::creusot_std::__stubs::mode()
        }
        .into()),
        Term::__Nonexhaustive => todo!(),
    }
}

fn encode_term_with_triggers_(
    term: &TermWithTriggers,
    locals: &mut Locals,
) -> Result<TokenStream, EncodeError> {
    let ts = encode_term_(&term.term, locals)?.toks();
    encode_trigger_(&term.trigger, ts, locals)
}

fn encode_trigger_(
    mut trigger: &[Trigger],
    mut ts: TokenStream,
    locals: &mut Locals,
) -> Result<TokenStream, EncodeError> {
    while let [rest @ .., last] = trigger {
        trigger = rest;
        let terms_span = last.terms.span();
        let trigs = last
            .terms
            .iter()
            .map(|t| Ok(encode_term_(t, locals)?.toks()))
            .collect::<Result<Vec<_>, _>>()?;
        ts = TokenStream::from_iter([
            quote_spanned! { span_before(last.span()) => ::creusot_std::__stubs:: },
            quote_spanned! { last.trigger_token.span() => trigger },
            quote_spanned! { terms_span => ((#(#trigs,)*), #ts) },
        ])
    }
    Ok(ts)
}

fn encode_block_(block: &TermBlock, locals: &mut Locals) -> TokenStream {
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

pub fn encode_block(block: &TermBlock) -> TokenStream {
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
                pattern_bind(pat, locals, stmt.span())?;
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

impl<'a> Visit<'a> for PatEncoder<'a> {
    fn visit_pat(&mut self, pat: &'a Pat) {
        match pat {
            Pat::Path(path) if let Some(ident) = path.path.get_ident() => {
                self.locals.bind_raw(ident)
            }
            Pat::Ident(ident) => self.locals.bind_raw(&ident.ident),
            Pat::Lit(syn::ExprLit { lit: Lit::Int(_), .. }) => {
                self.has_literal_int = true;
                visit_pat(self, pat)
            }
            _ => visit_pat(self, pat),
        }
    }
}

/// `bind_raw` on every variable in `pat`
fn pattern_bind<'a>(pat: &'a Pat, locals: &'a mut Locals, span: Span) -> Result<(), EncodeError> {
    let mut encoder = PatEncoder::new(locals);
    encoder.visit_pat(pat);

    if encoder.has_literal_int {
        Err(EncodeError::Unsupported(span, "Pattern matching literals on Int are unsupported by Pearlite. Consider using if-then-else instead.".to_string()))
    } else {
        Ok(())
    }
}

fn encode_arm_(arm: &TermArm, locals: &mut Locals) -> Result<TokenStream, EncodeError> {
    if arm.guard.is_some() {
        return Err(EncodeError::Unsupported(arm.span(), "match guard".to_string()));
    }
    let comma = &arm.comma;
    let pat = &arm.pat;
    locals.open();
    pattern_bind(pat, locals, arm.span())?;
    let body = encode_term_(&arm.body, locals)?.toks();
    locals.close();
    Ok(quote_spanned! {arm.span()=> #pat => #body #comma })
}

// check the output of various builtin creusot operators
#[cfg(test)]
mod tests {
    use super::*;

    const IMPORTS: &str = "# [allow (unused)] use :: creusot_std :: __stubs :: { IndexLogicStub as _ , ViewStub as _ }";

    #[track_caller]
    fn check_term(term: TokenStream, reference: &str) {
        assert_eq!(term.to_string(), format!("{{ {IMPORTS} ; {reference} }}"))
    }

    #[test]
    fn encode_old() {
        let term: Term = syn::parse_str("old(x)").unwrap();

        check_term(encode_term(&term), "* :: creusot_std :: __stubs :: old (* & x ,)");
    }

    #[test]
    fn encode_fin() {
        let term: Term = syn::parse_str("^ x").unwrap();
        check_term(encode_term(&term), "* :: creusot_std :: logic :: ops :: Fin :: fin (* & x)");

        let term: Term = syn::parse_str("^ ^ x").unwrap();
        check_term(
            encode_term(&term),
            "* :: creusot_std :: logic :: ops :: Fin :: fin (* :: creusot_std :: logic :: ops :: Fin :: fin (* & x))",
        );
    }

    #[test]
    fn encode_cur() {
        let term: Term = syn::parse_str("*x").unwrap();
        check_term(encode_term(&term), "* & * (x)");
        let term: Term = syn::parse_str("* ^ x").unwrap();

        check_term(
            encode_term(&term),
            "* (* :: creusot_std :: logic :: ops :: Fin :: fin (* & x))",
        );
    }

    #[test]
    fn encode_forall() {
        let term: Term = syn::parse_str("forall<x: Int> x == x").unwrap();
        check_term(
            encode_term(&term),
            ":: creusot_std :: __stubs :: forall (# [creusot :: no_translate] # [creusot :: logic_closure] | x : & Int , | :: creusot_std :: __stubs :: equal (* x , * x))",
        );

        let term: Term = syn::parse_str("forall<x: Int> forall<y: Int> true").unwrap();
        check_term(
            encode_term(&term),
            ":: creusot_std :: __stubs :: forall (# [creusot :: no_translate] # [creusot :: logic_closure] | x : & Int , | :: creusot_std :: __stubs :: forall (# [creusot :: no_translate] # [creusot :: logic_closure] | y : & Int , | true))",
        );
    }

    #[test]
    fn encode_exists() {
        let term: Term = syn::parse_str("exists<x:Int> x == x").unwrap();
        check_term(
            encode_term(&term),
            ":: creusot_std :: __stubs :: exists (# [creusot :: no_translate] # [creusot :: logic_closure] | x : & Int , | :: creusot_std :: __stubs :: equal (* x , * x))",
        );

        let term: Term = syn::parse_str("exists<x:Int> exists<y:Int> true").unwrap();
        check_term(
            encode_term(&term),
            ":: creusot_std :: __stubs :: exists (# [creusot :: no_translate] # [creusot :: logic_closure] | x : & Int , | :: creusot_std :: __stubs :: exists (# [creusot :: no_translate] # [creusot :: logic_closure] | y : & Int , | true))",
        );
    }

    #[test]
    fn encode_impl() {
        let term: Term = syn::parse_str("false ==> true").unwrap();
        check_term(encode_term(&term), ":: creusot_std :: __stubs :: implication (false , true)");
    }
}
