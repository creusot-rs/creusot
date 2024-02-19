use crate::{declaration::Use, ty::Type, Ident};

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

pub enum Expr {
    /// Variables eg: `x`
    Symbol(Ident),
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

/// TODO: what is the bool?
pub struct Var(Ident, Term, Type, bool);

/// Parameter declarations
pub enum Param {
    Ty(Type),
    Term(Ident, Type),
    Region(Ident, Type),
    Cont(Ident, Vec<Ident>, Vec<Param>),
}

pub enum Arg {
    Ty(Type),
    Term(Term),
    Ref(Ident),
    Cont(Expr),
}

pub struct Defn {
    pub name: Ident,
    pub writes: Vec<Ident>,
    pub params: Vec<Param>,
    pub body: Expr,
}

pub enum Decl {
    /// Coma definitions
    Defn(Vec<Defn>),
    /// Escape hatch for type declarations, predicates etc...
    PureDecl(crate::declaration::Decl),
    Use(Use),
}

pub struct Module(pub Vec<Decl>);
