use crate::{declaration::Use, ty::Type, Ident, Print, QName};
use pretty::docs;

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

type Term = crate::Exp;

/// The Coma Intermediate Verification Language
///
/// This language is developed by Paul Patault, Andrei Paskeivich and Jean-Christophe Filiatre.
/// In this module is a complete, faithful ast and pretty printer for Coma.
///
/// TODO: Document Coma and its motivation
///
/// Notable points
///
/// 1. Higher order functional language that always generates first-order VCs
/// 2. User level control on transparency of functions
/// 3. CPS structure

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Expr {
    /// Variables eg: `x`
    Symbol(QName),
    /// Generic application for type lambdas, terms, references and continuations
    /// e <ty>... t... | e...
    App(Box<Expr>, Box<Arg>),
    /// Functions, used for anonymous closures
    /// fun pl -> e
    Lambda(Vec<Param>, Box<Expr>),
    /// Handler group definitions, binds a set of (mutually recursive) handlers
    /// Can be read as a "where" clause in haskell.
    //
    /// e / rec? h p e and ...
    Defn(Box<Expr>, bool, Vec<Defn>),
    /// Similarly to handlers, the assignment should be read "backwards", the expression happens in a context where
    /// the identifiers have been updated
    Assign(Box<Expr>, Vec<(Ident, Term)>),
    /// Let binding, introduces a new lexical scope.
    Let(Box<Expr>, Vec<Var>),
    /// Asserts that the term holds before evaluating the expression
    Assert(Box<Term>, Box<Expr>),
    /// Syntactic sugar for assuming that a term holds before evaluating the inner expression
    Assume(Box<Term>, Box<Expr>),
    /// The core operator of coma is the "black box" or *abstraction barrier* operator.
    /// This operator distinguishes the responsibility between the caller and callee for
    /// verification. Everything under an abstraction is opaque to the outside world, whereas from the inside,
    /// we can suppose than any surrounding assertions hold.
    //
    /// TODO: Write a more intuitive explanaitio
    //
    /// ! e
    BlackBox(Box<Expr>),
    /// Good question...
    WhiteBox(Box<Expr>),
    /// A non-deterministic value
    Any,
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Var(pub Ident, pub Type, pub Term, pub IsRef);

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum IsRef {
    Ref,
    NotRef,
}

/// Parameter declarations
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Param {
    // Can only be type parameters
    Ty(Type),
    Term(Ident, Type),
    Reference(Ident, Type),
    /// Continuations accept a set of handlers and a set of ordinary parameters
    Cont(Ident, Vec<Ident>, Vec<Param>),
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Arg {
    /// Type application
    Ty(Type),
    /// Logical terms (and 'program' ones)
    Term(Term),
    /// Reference
    Ref(Ident),
    /// Continuation parameter
    Cont(Expr),
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Defn {
    pub name: Ident,
    /// Only relevant if using references
    pub writes: Vec<Ident>,
    pub params: Vec<Param>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Decl {
    /// Coma definitions
    Defn(Vec<Defn>),
    /// Escape hatch for type declarations, predicates etc...
    PureDecl(crate::declaration::Decl),
    Use(Use),
}

#[derive(Clone, Debug)]
pub struct Module(pub Vec<Decl>);

impl Expr {
    pub fn app(self, args: Vec<Arg>) -> Self {
        args.into_iter().fold(self, |acc, a| Expr::App(Box::new(acc), Box::new(a)))
    }

    pub fn assign(mut self, lhs: Ident, rhs: Term) -> Self {
        match &mut self {
            Expr::Assign(_, asgns) => {
                asgns.push((lhs, rhs));
                self
            }
            _ => Expr::Assign(Box::new(self), vec![(lhs, rhs)]),
        }
    }
}

impl Print for Param {
    fn pretty<'b, 'a: 'b, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Param::Ty(ty) => ty.pretty(alloc),
            Param::Term(id, ty) => docs![alloc, id.pretty(alloc), ":", ty.pretty(alloc)].parens(),
            Param::Reference(id, ty) => docs![alloc, "&", id.pretty(alloc), ":", ty.pretty(alloc)],
            Param::Cont(id, writes, params) => docs![
                alloc,
                id.pretty(alloc),
                alloc.space(),
                brackets(alloc.intersperse(writes.iter().map(|a| a.pretty(alloc)), " ")),
                alloc.space(),
                alloc.intersperse(params.iter().map(|a| a.pretty(alloc)), " "),
            ]
            .parens(),
        }
    }
}
impl Print for Var {
    fn pretty<'b, 'a: 'b, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        docs![
            alloc,
            if matches!(self.3, IsRef::Ref) { alloc.text("& ") } else { alloc.nil() },
            self.0.pretty(alloc),
            " : ",
            self.1.pretty(alloc),
            " = ",
            self.2.pretty(alloc)
        ]
    }
}

impl Print for Arg {
    fn pretty<'b, 'a: 'b, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Arg::Ty(ty) => ty.pretty(alloc).enclose("<", ">"),
            Arg::Term(t) => t.pretty(alloc).braces(),
            Arg::Ref(r) => alloc.text("& ").append(r.pretty(alloc)),
            Arg::Cont(e @ Expr::Lambda(_, _)) => e.pretty(alloc),
            Arg::Cont(c) => c.pretty(alloc).parens(),
        }
    }
}

impl Print for Expr {
    fn pretty<'b, 'a: 'b, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Expr::Symbol(id) => id.pretty(alloc),
            Expr::App(e, arg) => {
                let needs_paren = !matches!(
                    &**e,
                    Expr::App(_, _) | Expr::Symbol(_) | Expr::Any | Expr::Lambda(_, _)
                );

                let doc = e.pretty(alloc);

                docs![
                    alloc,
                    if needs_paren { doc.parens() } else { doc },
                    alloc.softline(),
                    arg.pretty(alloc)
                ]
            }
            Expr::Lambda(params, body) => {
                let header = if params.is_empty() {
                    alloc.text("-> ")
                } else {
                    docs![
                        alloc,
                        "fun ",
                        alloc.intersperse(params.iter().map(|p| p.pretty(alloc)), alloc.text(" ")),
                        alloc.text(" -> ")
                    ]
                };

                header.append(body.pretty(alloc).nest(2)).parens()
            }
            Expr::Defn(cont, rec, handlers) => {
                let handlers =
                    handlers.iter().map(|d| print_defn(d, if *rec { "=" } else { "->" }, alloc));
                cont.pretty(alloc).append(alloc.softline()).append(bracket_list(
                    alloc,
                    handlers,
                    alloc.line().append(alloc.text("| ")),
                ))
            }
            Expr::Let(cont, lets) => docs![
                alloc,
                cont.pretty(alloc),
                bracket_list(
                    alloc,
                    lets.iter().map(|l| l.pretty(alloc)),
                    alloc.line().append(alloc.text("| "))
                )
            ],
            Expr::Assign(cont, asgns) => docs![
                alloc,
                bracket_list(
                    alloc,
                    asgns.iter().map(|(id, t)| docs![
                        alloc,
                        "&",
                        id.pretty(alloc),
                        alloc.space(),
                        "<-",
                        alloc.space(),
                        t.pretty(alloc)
                    ]),
                    alloc.line().append(alloc.text("| "))
                ),
                cont.pretty(alloc)
            ],
            Expr::Assert(t, e) => {
                docs![alloc, t.pretty(alloc).braces(), alloc.space(), e.pretty(alloc)]
            }
            Expr::Assume(t, e) => {
                docs![alloc, t.pretty(alloc).enclose("-{", "}-"), alloc.space(), e.pretty(alloc)]
            }
            Expr::BlackBox(e) => docs![alloc, "!", alloc.space(), e.pretty(alloc)].parens(),
            Expr::WhiteBox(e) => docs![alloc, "?", alloc.space(), e.pretty(alloc)].parens(),
            Expr::Any => alloc.text("any"),
        }
    }
}

fn brackets<'a, A: pretty::DocAllocator<'a>>(
    doc: pretty::DocBuilder<'a, A>,
) -> pretty::DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    if !matches!(&*doc.1, pretty::Doc::Nil) {
        doc.brackets().nest(2)
    } else {
        doc
    }
}

fn bracket_list<'a, S, A: pretty::DocAllocator<'a>>(
    alloc: &'a A,
    docs: impl Iterator<Item = pretty::DocBuilder<'a, A>>,
    sep: S,
) -> pretty::DocBuilder<'a, A>
where
    S: pretty::Pretty<'a, A> + Clone,
{
    let body = alloc.intersperse(docs, sep).group();
    if matches!(&*body.1, pretty::Doc::Nil) {
        return body;
    }

    docs![
        alloc,
        alloc.line_(),
        alloc.space().append(body).append(alloc.space()).brackets().nest(0),
        alloc.line_()
    ]
    .group()
}

fn print_defn<'a, A: pretty::DocAllocator<'a>>(
    defn: &'a Defn,
    arrow_kind: &'a str,
    alloc: &'a A,
) -> pretty::DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    docs![
        alloc,
        defn.name.pretty(alloc),
        alloc.space(),
        bracket_list(alloc, defn.writes.iter().map(|a| a.pretty(alloc)), " "),
        if defn.writes.is_empty() { alloc.nil() } else { alloc.space() },
        alloc.intersperse(defn.params.iter().map(|a| a.pretty(alloc)), " "),
        arrow_kind,
        alloc.space(),
        defn.body.pretty(alloc).nest(2),
    ]
}

impl Print for Defn {
    fn pretty<'b, 'a: 'b, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        docs![alloc, "let ", print_defn(self, "=", alloc),]
    }
}
