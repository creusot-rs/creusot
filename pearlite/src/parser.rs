/// Parse a term from a syn tree
use syn::Term as RT;

use crate::term::{Ident, Term::*, *};

pub trait Resolver {
    fn resolve(&self, _: &[String]) -> Option<Name>;
}

#[derive(Debug)]
pub enum ParseError {
    UnhandledSyntax(RT),
    Other(String),
    Syn(syn::Error),
    UnknownIdentifier(Vec<String>),
    Generic,
}

impl From<syn::Error> for ParseError {
    fn from(err: syn::Error) -> Self {
        Syn(err)
    }
}

use ParseError::*;

impl Term {
    pub fn from_syn<R: Resolver>(res: &R, term: RT) -> Result<Term, ParseError> {
        use syn::term::{
            TermBinary, TermBlock, TermCall, TermCast, TermExists, TermFinal, TermForall, TermIf,
            TermImpl, TermLit, TermMatch, TermParen, TermPath, TermTuple, TermUnary,
        };
        match term {
            RT::Match(TermMatch { box expr, arms, .. }) => Ok(Match {
                expr: box Term::from_syn(res, expr)?,
                arms: arms
                    .into_iter()
                    .map(|m| MatchArm::from_syn(res, m))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            RT::Path(TermPath { path, .. }) => Ok(Variable { path: Name::from_syn(res, path)? }),
            RT::Lit(TermLit { lit }) => {
                use crate::term::Literal::*;
                use syn::{Lit as RL, LitBool};
                match lit {
                    RL::Int(lit) => match lit.suffix() {
                        "u8" => Ok(Term::Lit { lit: U8(lit.base10_parse()?) }),
                        "u16" => Ok(Term::Lit { lit: U16(lit.base10_parse()?) }),
                        "u32" => Ok(Term::Lit { lit: U32(lit.base10_parse()?) }),
                        "u64" => Ok(Term::Lit { lit: U64(lit.base10_parse()?) }),
                        "usize" => Ok(Term::Lit { lit: Usize(lit.base10_parse()?) }),
                        _ => Ok(Term::Lit { lit: Int(lit.base10_parse()?) }),
                    },
                    RL::Float(lit) => match lit.suffix() {
                        "f32" => Ok(Term::Lit { lit: F32(lit.base10_parse()?) }),
                        "f64" => Ok(Term::Lit { lit: F64(lit.base10_parse()?) }),
                        _ => Err(Other("unsupported float type".into())),
                    },
                    RL::Bool(LitBool { value, .. }) => Ok(Term::Lit { lit: Bool(value) }),
                    _ => Err(Other("unsupported literal".into())),
                }
            }
            RT::Tuple(TermTuple { elems, .. }) => Ok(Tuple {
                elems: elems
                    .into_iter()
                    .map(|t| Term::from_syn(res, t))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            RT::Binary(TermBinary { box left, op, box right }) => Ok(Binary {
                left: box Term::from_syn(res, left)?,
                op: BinOp::from_syn(op)?,
                right: box Term::from_syn(res, right)?,
            }),
            RT::Impl(TermImpl { box hyp, box cons, .. }) => Ok(Binary {
                left: box Term::from_syn(res, hyp)?,
                op: BinOp::Impl,
                right: box Term::from_syn(res, cons)?,
            }),
            RT::Forall(TermForall { args, box term, .. }) => {
                use syn::QuantArg;
                let mut targs = Vec::new();
                for QuantArg { ident, box ty, .. } in args {
                    targs.push((Ident::from_syn(ident)?, Type::from_syn(res, ty)?));
                }

                Ok(Forall { args: targs, body: box Term::from_syn(res, term)? })
            }
            RT::Exists(TermExists { args, box term, .. }) => {
                use syn::QuantArg;
                let mut targs = Vec::new();
                for QuantArg { ident, box ty, .. } in args {
                    targs.push((Ident::from_syn(ident)?, Type::from_syn(res, ty)?));
                }

                Ok(Exists { args: targs, body: box Term::from_syn(res, term)? })
            }
            RT::Block(TermBlock { block, .. }) => Self::from_tblock(res, block),
            RT::Paren(TermParen { box expr, .. }) => Term::from_syn(res, expr),
            RT::Call(TermCall { box func, args, .. }) => {
                if let RT::Path(TermPath { path, .. }) = func {
                    Ok(Call {
                        func: Name::from_syn(res, path)?,
                        args: args
                            .into_iter()
                            .map(|t| Term::from_syn(res, t))
                            .collect::<Result<Vec<_>, _>>()?,
                    })
                } else {
                    Err(Generic)
                }
            }
            RT::Final(TermFinal { box term, .. }) => {
                Ok(Unary { op: UnOp::Final, expr: box Term::from_syn(res, term)? })
            }
            RT::Unary(TermUnary { op, box expr }) => {
                let expr = Term::from_syn(res, expr)?;

                let op = match op {
                    syn::UnOp::Deref(_) => UnOp::Deref(None),
                    syn::UnOp::Neg(_) => UnOp::Neg,
                    syn::UnOp::Not(_) => UnOp::Not,
                };

                Ok(Unary { op, expr: box expr })
            }
            RT::Absurd(_) => Ok(Absurd),
            RT::Cast(TermCast { box expr, box ty, .. }) => {
                Ok(Cast { expr: box Term::from_syn(res, expr)?, ty: Type::from_syn(res, ty)? })
            }
            RT::If(TermIf {
                box cond,
                then_branch,
                else_branch: Some((_, box else_branch)),
                ..
            }) => {
                let cond = Term::from_syn(res, cond)?;
                let then_branch = Self::from_tblock(res, then_branch)?;
                let else_branch = Self::from_syn(res, else_branch)?;

                Ok(If {
                    cond: box cond,
                    then_branch: box then_branch,
                    else_branch: box else_branch,
                })
            }
            t => unimplemented!("{:?}", t),
        }
    }

    fn from_term_stmt<R: Resolver>(
        res: &R,
        stmt: syn::TermStmt,
        inner: Term,
    ) -> Result<Term, ParseError> {
        use syn::{TLocal, TermStmt::*};
        match stmt {
            Local(TLocal { pat, init: Some((_, box arg)), .. }) => Ok(Let {
                pat: Pattern::from_syn(res, pat)?,
                arg: box Term::from_syn(res, arg)?,
                body: box inner,
            }),
            Expr(t) => Term::from_syn(res, t),
            Semi(t, _) => {
                Ok(Let { pat: Pattern::Wild, arg: box Term::from_syn(res, t)?, body: box inner })
            }
            _ => Err(Generic),
        }
    }

    fn from_tblock<R: Resolver>(res: &R, block: syn::TBlock) -> Result<Term, ParseError> {
        let syn::TBlock { mut stmts, .. } = block;
        let mut exp = Term::from_term_stmt(res, stmts.remove(stmts.len() - 1), Term::unit())?;

        for s in stmts.into_iter().rev() {
            if let syn::TermStmt::Expr(_) = s {
                return Err(Generic);
            };
            exp = Term::from_term_stmt(res, s, exp)?;
        }

        Ok(exp)
    }
}

impl Type {
    pub fn from_syn<R: Resolver>(res: &R, ty: syn::Type) -> Result<Self, ParseError> {
        use syn::Type as T;
        use syn::{TypeParen, TypePath, TypeReference, TypeTuple};
        match ty {
            T::Paren(TypeParen { box elem, .. }) => Type::from_syn(res, elem),
            T::Path(TypePath { path, .. }) => {
                let name = Name::from_syn(res, path)?;
                use crate::term::{LitTy::*, Size::*};

                match name {
                    Name::Ident(name) => match &name[..] {
                        "bool" => Ok(Type::Lit(Boolean)),
                        "u8" => Ok(Type::Lit(Unsigned(Eight))),
                        "u16" => Ok(Type::Lit(Unsigned(Sixteen))),
                        "u32" => Ok(Type::Lit(Unsigned(ThirtyTwo))),
                        "u64" => Ok(Type::Lit(Unsigned(SixtyFour))),
                        "usize" => Ok(Type::Lit(Unsigned(Mach))),
                        "i8" => Ok(Type::Lit(Signed(Eight))),
                        "i16" => Ok(Type::Lit(Signed(Sixteen))),
                        "i32" => Ok(Type::Lit(Signed(ThirtyTwo))),
                        "i64" => Ok(Type::Lit(Signed(SixtyFour))),
                        "f32" => Ok(Type::Lit(Float)),
                        "f64" => Ok(Type::Lit(Double)),
                        _ => Err(Generic),
                    },
                    Name::Path { path, name, .. } if path[0] == "creusot_contracts" => {
                        if name == "Int" {
                            Ok(Type::Lit(LitTy::Integer))
                        } else {
                            Err(Generic)
                        }
                    }
                    _ => Ok(Type::Path { path: name }),
                }
            }
            T::Reference(TypeReference { mutability, box elem, .. }) => {
                if mutability.is_some() {
                    Ok(Type::Reference { kind: RefKind::Mut, ty: box Type::from_syn(res, elem)? })
                } else {
                    Ok(Type::Reference { kind: RefKind::Not, ty: box Type::from_syn(res, elem)? })
                }
            }
            T::Tuple(TypeTuple { elems, .. }) => Ok(Type::Tuple {
                elems: elems
                    .into_iter()
                    .map(|t| Type::from_syn(res, t))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            _ => Err(Other("unsupported type".into())),
        }
    }
}

impl BinOp {
    pub fn from_syn(op: syn::BinOp) -> Result<Self, ParseError> {
        use BinOp::*;
        match op {
            syn::BinOp::Add(_) => Ok(Add),
            syn::BinOp::Sub(_) => Ok(Sub),
            syn::BinOp::Mul(_) => Ok(Mul),
            syn::BinOp::Div(_) => Ok(Div),
            // syn::BinOp::Rem(_) => { Ok(Rem) }
            syn::BinOp::And(_) => Ok(And),
            syn::BinOp::Or(_) => Ok(Or),
            // syn::BinOp::BitXor(_) => { Ok(BitXor) }
            // syn::BinOp::BitAnd(_) => { Ok(BitAnd) }
            // syn::BinOp::BitOr(_) => { Ok(BitOr) }
            // syn::BinOp::Shl(_) => { Ok(Shl) }
            // syn::BinOp::Shr(_) => { Ok(Shr) }
            syn::BinOp::Eq(_) => Ok(Eq),
            syn::BinOp::Lt(_) => Ok(Lt),
            syn::BinOp::Le(_) => Ok(Le),
            syn::BinOp::Ne(_) => Ok(Ne),
            syn::BinOp::Ge(_) => Ok(Ge),
            syn::BinOp::Gt(_) => Ok(Gt),
            _ => Err(Other("unsupported binary operation".into())),
        }
    }
}

impl Name {
    pub fn from_syn<R: Resolver>(res: &R, path: syn::Path) -> Result<Self, ParseError> {
        let mut seg = Vec::new();
        use syn::PathArguments::*;

        for segment in &path.segments {
            match segment.arguments {
                None => seg.push(segment.ident.to_string()),
                _ => return Err(Other("unexpected arguments in path".into())),
            }
        }

        match res.resolve(&seg) {
            Some(p) => Ok(p),
            Option::None => {
                if seg.len() == 1 {
                    Ok(Name::Ident(seg.remove(0)))
                } else {
                    Err(UnknownIdentifier(seg))
                }
            }
        }
    }
}

impl Ident {
    pub fn from_syn(id: syn::Ident) -> Result<Self, ParseError> {
        Ok(Ident(id.to_string()))
    }
}

impl Pattern {
    pub fn from_syn<R: Resolver>(res: &R, pat: syn::Pat) -> Result<Self, ParseError> {
        use syn::{PatTuple, PatTupleStruct};
        // use syn::{PatIdent, PatStruct, PatTuple, PatTupleStruct, PatWild};
        match pat {
            // Core
            syn::Pat::Ident(pat) => {
                if pat.by_ref.is_some() || pat.mutability.is_some() || pat.subpat.is_some() {
                    return Err(Generic);
                }

                match res.resolve(&[pat.ident.to_string()]) {
                    Some(path) => Ok(Pattern::TupleStruct { path, fields: vec![] }),
                    None => Ok(Pattern::Var(Ident::from_syn(pat.ident)?)),
                }
            }
            syn::Pat::Struct(pat) => {
                let mut fields = Vec::new();
                for fld in pat.fields.into_iter() {
                    if let syn::Member::Named(id) = fld.member {
                        fields.push((Ident::from_syn(id)?, Pattern::from_syn(res, *fld.pat)?));
                    } else {
                        return Err(Generic);
                    }
                }

                Ok(Pattern::Struct { path: Name::from_syn(res, pat.path)?, fields })
            }
            // syn::Pat::Tuple(PatTuple {..}) => {}
            syn::Pat::TupleStruct(PatTupleStruct { path, pat: PatTuple { elems, .. }, .. }) => {
                let fields = elems
                    .into_iter()
                    .map(|p| Pattern::from_syn(res, p))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Pattern::TupleStruct { path: Name::from_syn(res, path)?, fields })
            }
            syn::Pat::Wild(_) => Ok(Pattern::Wild),
            syn::Pat::Lit(syn::PatLit {
                expr: box syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Bool(b), .. }),
                ..
            }) => Ok(Pattern::Boolean(b.value)),

            // Medium or less useful
            syn::Pat::Path(_) | syn::Pat::Or(_) | syn::Pat::Type(_) => Err(Other("medium".into())),

            // Difficult or unclear how to implement
            syn::Pat::Lit(_)
            | syn::Pat::Reference(_)
            | syn::Pat::Box(_)
            | syn::Pat::Slice(_)
            | syn::Pat::Rest(_)
            | syn::Pat::Range(_) => Err(Other("hard".into())),

            _ => Err(Other(format!("{:?}", pat))),
        }
    }
}

impl MatchArm {
    pub fn from_syn<R: Resolver>(res: &R, arm: syn::TermArm) -> Result<Self, ParseError> {
        if arm.guard.is_some() {
            return Err(Other("guards are unsupported".into()));
        }
        Ok(MatchArm {
            pat: Pattern::from_syn(res, arm.pat)?,
            body: box Term::from_syn(res, *arm.body)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::term::*;

    #[test]
    fn parse_match() {
        struct DummyR;
        impl super::Resolver for DummyR {
            fn resolve(&self, p: &[String]) -> Option<Name> {
                Some(Name::Path { path: vec![], name: p[0].clone(), id: 0 })
            }
        }
        let term = syn::parse_quote! {
            match 2u32 {
                Cons(_, _) => { true }
                Nil => 1u32 + 2.0f32
            }
        };

        Term::from_syn(&DummyR, term).unwrap();
    }
}
