use crate::{
    Ident, Name, QName,
    declaration::{Attribute, Use},
    printer::{Print, Why3Scope},
    ty::Type,
};

use pretty::docs;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

pub type Term = crate::Exp;

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
    Name(Name),
    /// Generic application for type lambdas, terms, references and continuations
    ///
    /// ```ignore
    /// e <ty>... t... | e...
    /// ```
    App(Box<Expr>, Box<Arg>),
    /// Functions, used for anonymous closures
    /// fun pl -> e
    Lambda(Box<[Param]>, Box<Expr>),
    /// Handler group definitions, binds a set of (mutually recursive) handlers
    /// Can be read as a "where" clause in haskell.
    ///
    /// e / rec? h p e and ...
    Defn(Box<Expr>, bool, Box<[Defn]>),
    /// Similarly to handlers, the assignment should be read "backwards", the expression happens in a context where
    /// the identifiers have been updated
    Assign(Box<Expr>, Box<[(Ident, Term)]>),
    /// Let binding, introduces a new lexical scope.
    Let(Box<Expr>, Box<[Var]>),
    /// Asserts that the term holds before evaluating the expression
    Assert(Box<Term>, Box<Expr>),
    /// Syntactic sugar for assuming that a term holds before evaluating the inner expression
    Assume(Box<Term>, Box<Expr>),
    /// The core operator of coma is the "black box" or *abstraction barrier* operator.
    /// This operator distinguishes the responsibility between the caller and callee for
    /// verification. Everything under an abstraction is opaque to the outside world, whereas from the inside,
    /// we can suppose than any surrounding assertions hold.
    ///
    // TODO: Write a more intuitive explanation
    //
    /// `! e`
    BlackBox(Box<Expr>),
    /// Good question...
    ///
    /// This operator exists in Coma's surface syntax, but it is (almost?) never needed for the user (us).
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
    Cont(Ident, Box<[Ident]>, Box<[Param]>),
}

impl Param {
    pub fn as_term(&self) -> (Ident, &Type) {
        if let Param::Term(id, ty) = self { (*id, ty) } else { panic!("not a term") }
    }
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

/// The signature of a coma handler.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Prototype {
    /// Name of the handler
    pub name: Ident,
    /// optional attributes, like `[@coma:extspec]`
    pub attrs: Vec<Attribute>,
    /// Arguments (and continuations) of the handler
    pub params: Box<[Param]>,
}

impl Prototype {
    pub fn new(name: Ident, params: impl Into<Box<[Param]>>) -> Self {
        Prototype { name, attrs: vec![], params: params.into() }
    }
}

/// A coma handler, introduced with `let`.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Defn {
    pub prototype: Prototype,
    pub body: Expr,
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Decl {
    /// Coma definitions
    Defn(Box<[Defn]>),
    /// Escape hatch for type declarations, predicates etc...
    PureDecl(crate::declaration::Decl),
    Use(Use),
}

#[derive(Clone, Debug)]
pub struct Module(pub Box<[Decl]>);

impl Defn {
    pub fn simple(name: Ident, body: Expr) -> Self {
        Defn { prototype: Prototype { name: name, attrs: vec![], params: Box::new([]) }, body }
    }
}

impl Expr {
    pub fn var(name: Ident) -> Self {
        Expr::Name(Name::local(name))
    }

    pub fn constant(name: QName) -> Self {
        Expr::Name(Name::Global(name))
    }

    pub fn boxed(self) -> Box<Self> {
        Box::new(self)
    }

    pub fn app(self, args: impl IntoIterator<Item = Arg>) -> Self {
        args.into_iter().fold(self, |acc, a| Expr::App(Box::new(acc), Box::new(a)))
    }

    pub fn assign(self, lhs: Ident, rhs: Term) -> Self {
        Expr::Assign(Box::new(self), Box::new([(lhs, rhs)]))
    }

    pub fn assert(cond: Term, k: Expr) -> Self {
        Expr::Assert(Box::new(cond), Box::new(k))
    }

    pub fn assume(cond: Term, k: Expr) -> Self {
        Expr::Assume(Box::new(cond), Box::new(k))
    }

    pub fn black_box(self) -> Self {
        Expr::BlackBox(Box::new(self))
    }

    pub fn let_(self, vars: impl IntoIterator<Item = Var>) -> Self {
        Expr::Let(Box::new(self), vars.into_iter().collect())
    }

    /// Adds a set of mutually recursive where bindings around `self`
    pub fn where_(self, defs: Box<[Defn]>) -> Self {
        // If we have `x [ x = z ]` replace this by `z`
        if defs.len() == 1
            && !defs[0].body.occurs(&defs[0].prototype.name)
            && self.as_variable().is_some_and(|qn| qn == &defs[0].prototype.name)
        {
            let [d] = *defs.into_array::<1>().unwrap();
            d.body
        } else {
            Expr::Defn(Box::new(self), true, defs)
        }
    }

    pub fn as_variable(&self) -> Option<&Ident> {
        if let Expr::Name(Name::Local(nm, None)) = self { Some(nm) } else { None }
    }

    /// Checks whether the expression is protected by a black box.
    ///
    /// It allows the box to be surrounded by assertions
    pub fn is_guarded(&self) -> bool {
        match self {
            Expr::Assert(_, e) => e.is_guarded(),
            Expr::Defn(e, _, _) => e.is_guarded(),
            Expr::BlackBox(_) => true,
            _ => false,
        }
    }

    /// Checks whether a symbol of name `cont` occurs in `self`
    pub fn occurs(&self, cont: &Ident) -> bool {
        match self {
            Expr::Name(Name::Local(v, _)) => v == cont,
            Expr::Name(Name::Global(_)) => false,
            Expr::App(e, arg) => {
                let arg = if let Arg::Cont(e) = &**arg { e.occurs(cont) } else { false };
                arg || e.occurs(cont)
            }
            Expr::Lambda(params, body) => {
                let in_params = params
                    .iter()
                    .filter_map(|p| if let Param::Cont(n, _, _) = &*p { Some(n) } else { None })
                    .any(|n| n == cont);
                !in_params && body.occurs(cont)
            }
            Expr::Defn(e, _, defs) => {
                e.occurs(cont)
                    || defs.iter().any(|d| {
                        let in_params = d
                            .prototype
                            .params
                            .iter()
                            .filter_map(
                                |p| if let Param::Cont(n, _, _) = &*p { Some(n) } else { None },
                            )
                            .any(|n| n == cont);
                        !in_params && d.body.occurs(cont)
                    })
            }
            Expr::Assign(e, _) => e.occurs(cont),
            Expr::Let(e, _) => e.occurs(cont),
            Expr::Assert(_, e) | Expr::Assume(_, e) => e.occurs(cont),
            Expr::BlackBox(e) | Expr::WhiteBox(e) => e.occurs(cont),
            Expr::Any => false,
        }
    }
}

impl Print for Param {
    fn pretty<'a, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Param::Ty(ty) => docs![alloc, "< ", ty.pretty(alloc, scope), " >"],
            Param::Term(id, ty) => {
                scope.bind_value(*id);
                docs![alloc, id.pretty_value_name(alloc, scope), ":", ty.pretty(alloc, scope)]
                    .parens()
            }
            Param::Reference(id, ty) => {
                scope.bind_value(*id);
                docs![alloc, "&", id.pretty_value_name(alloc, scope), ":", ty.pretty(alloc, scope)]
            }
            Param::Cont(id, writes, params) => {
                scope.bind_value(*id);
                // Open a throwaway scope to bind the `params` (those names mean nothing)
                scope.open();
                let doc = docs![
                    alloc,
                    id.pretty_value_name(alloc, scope),
                    alloc.space(),
                    brackets(alloc.intersperse(
                        writes.iter().map(|a| a.pretty_value_name(alloc, scope)),
                        " "
                    )),
                    alloc.space(),
                    alloc.intersperse(params.iter().map(|a| a.pretty(alloc, scope)), " "),
                ]
                .parens();
                scope.close();
                doc
            }
        }
    }
}

impl Print for Var {
    fn pretty<'a, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.0);
        docs![
            alloc,
            if matches!(self.3, IsRef::Ref) { alloc.text("& ") } else { alloc.nil() },
            self.0.pretty_value_name(alloc, scope),
            ": ",
            self.1.pretty(alloc, scope),
            " = ",
            self.2.pretty(alloc, scope)
        ]
    }
}

impl Print for Arg {
    fn pretty<'a, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Arg::Ty(ty) => ty.pretty(alloc, scope).enclose("<", ">"),
            Arg::Term(t) => t.pretty(alloc, scope).braces(),
            Arg::Ref(r) => alloc.text("& ").append(r.pretty_value_name(alloc, scope)),
            Arg::Cont(e @ Expr::Lambda(_, _)) => e.pretty(alloc, scope),
            Arg::Cont(c) => c.pretty(alloc, scope).parens(),
        }
    }
}

impl Print for Expr {
    fn pretty<'a, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Expr::Name(name) => name.pretty_value_name(alloc, scope),
            Expr::App(e, arg) => {
                let mut args = vec![arg];

                let mut cur = e;
                while let Expr::App(e, arg) = &**cur {
                    cur = e;
                    args.push(arg);
                }
                args.reverse();
                let e = cur;

                let ix = args.partition_point(|arg| !matches!(&***arg, Arg::Cont(_)));
                let (ty_term, conts) = args.split_at(ix);

                let needs_paren = !matches!(
                    &**e,
                    Expr::App(_, _) | Expr::Name(_) | Expr::Any | Expr::Lambda(_, _)
                );

                let doc = e.pretty(alloc, scope);

                docs![
                    alloc,
                    docs![
                        alloc,
                        if needs_paren { doc.parens() } else { doc },
                        alloc.line(),
                        alloc.intersperse(
                            ty_term.iter().map(|a| a.pretty(alloc, scope)),
                            alloc.line()
                        )
                    ]
                    .group(),
                    if !ty_term.is_empty() && !conts.is_empty() {
                        alloc.line()
                    } else {
                        alloc.line_()
                    },
                    alloc.intersperse(conts.iter().map(|a| a.pretty(alloc, scope)), alloc.line()),
                ]
                .group()
                .nest(2)
            }
            Expr::Lambda(params, body) => {
                scope.open();
                let header = if params.is_empty() {
                    alloc.text("->")
                } else {
                    docs![
                        alloc,
                        "fun ",
                        alloc.intersperse(
                            params.iter().map(|p| p.pretty(alloc, scope)),
                            alloc.text(" ")
                        ),
                        alloc.text(" ->")
                    ]
                };
                let doc = header
                    .append(alloc.line())
                    .append(body.pretty(alloc, scope))
                    .group()
                    .nest(2)
                    .parens();
                scope.close();
                doc
            }
            Expr::Defn(cont, rec, handlers) => {
                scope.open();
                let doc = if *rec {
                    handlers.iter().for_each(|defn| scope.bind_value(defn.prototype.name));
                    cont.pretty(alloc, scope).append(bracket_list(
                        alloc,
                        handlers.iter().map(|d| print_rec_defn(d, alloc, scope)),
                        alloc.line().append(alloc.text("| ")),
                    ))
                } else {
                    // Print the handler bodies
                    let handlers: Box<[_]> =
                        handlers.iter().map(|d| print_nonrec_defn(d, alloc, scope)).collect();
                    // Bind the names of the handlers
                    let handlers: Box<[_]> =
                        handlers.into_iter().map(|d| d.pretty(alloc, scope)).collect();
                    // Print the main body
                    cont.pretty(alloc, scope).append(bracket_list(
                        alloc,
                        handlers.into_iter(),
                        alloc.line().append(alloc.text("| ")),
                    ))
                };
                scope.close();
                doc
            }
            Expr::Let(cont, lets) => {
                scope.open();
                let lets = bracket_list(
                    alloc,
                    lets.iter().map(|l| l.pretty(alloc, scope)),
                    alloc.line().append(alloc.text("| ")),
                );
                let doc = docs![alloc, cont.pretty(alloc, scope), lets,];
                scope.close();
                doc
            }
            Expr::Assign(cont, asgns) => {
                let needs_parens = matches!(&**cont, Expr::Let(_, _) | Expr::Defn(_, _, _));
                docs![
                    alloc,
                    bracket_list(
                        alloc,
                        asgns.iter().map(|(id, t)| docs![
                            alloc,
                            "&",
                            id.pretty_value_name(alloc, scope),
                            alloc.space(),
                            "<-",
                            alloc.space(),
                            t.pretty(alloc, scope)
                        ]),
                        alloc.line().append(alloc.text("| "))
                    ),
                    if asgns.is_empty() { alloc.nil() } else { alloc.line_() },
                    if needs_parens {
                        cont.pretty(alloc, scope).parens()
                    } else {
                        cont.pretty(alloc, scope)
                    }
                ]
            }
            Expr::Assert(t, e) => {
                docs![
                    alloc,
                    t.pretty(alloc, scope).braces().group(),
                    alloc.line(),
                    e.pretty(alloc, scope)
                ]
            }
            Expr::Assume(t, e) => {
                docs![
                    alloc,
                    t.pretty(alloc, scope).enclose("-{", "}-"),
                    alloc.line(),
                    e.pretty(alloc, scope)
                ]
            }
            Expr::BlackBox(e) => docs![alloc, "!", alloc.space(), e.pretty(alloc, scope)].parens(),
            Expr::WhiteBox(e) => docs![alloc, "?", alloc.space(), e.pretty(alloc, scope)].parens(),
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
    if !matches!(&*doc.1, pretty::Doc::Nil) { doc.brackets().nest(2) } else { doc }
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
        alloc.line(),
        alloc.space().append(body).append(alloc.space()).brackets().nest(0),
        alloc.line()
    ]
    .group()
}

/// The caller must have already bound the name of the definition.
/// That enables printing of recursive blocks, where all the names are in scope in all the bodies.
fn print_rec_defn<'a, A: pretty::DocAllocator<'a>>(
    defn: &'a Defn,
    alloc: &'a A,
    scope: &mut Why3Scope,
) -> pretty::DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    scope.open();
    let doc = docs![
        alloc,
        defn.prototype.name.pretty_value_name(alloc, scope),
        alloc.intersperse(
            defn.prototype.attrs.iter().map(|a| a.pretty(alloc, scope)),
            alloc.space()
        ),
        alloc.space(),
        alloc.intersperse(defn.prototype.params.iter().map(|a| a.pretty(alloc, scope)), " "),
        "=",
        alloc.space(),
        defn.body.pretty(alloc, scope).nest(2).group(),
    ];
    scope.close();
    doc
}

/// To print a non-recursive block of definitions, first render each body with `print_nonrec_defn`
/// while the names of the definitions are not in scope. Then call `pretty`, which binds these names.
struct NonRecDefnDoc<'a, A: pretty::DocAllocator<'a>> {
    name: Ident,
    attrs: pretty::DocBuilder<'a, A>,
    params: pretty::DocBuilder<'a, A>,
    body: pretty::DocBuilder<'a, A>,
}

impl<'a, A: pretty::DocAllocator<'a>> NonRecDefnDoc<'a, A> {
    fn pretty(self, alloc: &'a A, scope: &mut Why3Scope) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.name);
        docs![
            alloc,
            self.name.pretty_value_name(alloc, scope),
            self.attrs,
            alloc.space(),
            self.params,
            "->",
            alloc.space(),
            self.body
        ]
    }
}

fn print_nonrec_defn<'a, A: pretty::DocAllocator<'a>>(
    defn: &'a Defn,
    alloc: &'a A,
    scope: &mut Why3Scope,
) -> NonRecDefnDoc<'a, A>
where
    A::Doc: Clone,
{
    scope.open();
    let doc = NonRecDefnDoc {
        name: defn.prototype.name,
        attrs: alloc.intersperse(
            defn.prototype.attrs.iter().map(|a| a.pretty(alloc, scope)),
            alloc.space(),
        ),
        params: alloc
            .intersperse(defn.prototype.params.iter().map(|a| a.pretty(alloc, scope)), " "),
        body: defn.body.pretty(alloc, scope).nest(2).group(),
    };
    scope.close();
    doc
}

impl Print for Defn {
    fn pretty<'a, A: pretty::DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> pretty::DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.prototype.name);
        scope.open();
        let doc = docs![alloc, "let rec ", print_rec_defn(self, alloc, scope),];
        scope.close();
        doc
    }
}
