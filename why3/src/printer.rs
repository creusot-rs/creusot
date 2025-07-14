use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io::Write,
    iter::{once, repeat},
};

use crate::{
    Exp, Ident, Name, QName, Symbol,
    declaration::{
        self, AdtDecl, Attribute, Axiom, ConstructorDecl, Contract, Decl, DeclKind, FieldDecl,
        Goal, LogicDecl, LogicDefn, Meta, MetaArg, MetaIdent, Module, Predicate, Signature, Span,
        SumRecord, TyDecl, Use,
    },
    exp::{AssocDir, BinOp, Binder, Constant, Pattern, Precedence, Trigger, UnOp},
    ty::Type,
};
use num::{Float, Zero};
use pretty::*;

pub struct PrintDisplay<'a, A: Print>(&'a A);

impl<A: Print> Display for PrintDisplay<'_, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = BoxAllocator;
        self.0.pretty(&alloc, &mut Why3Scope::new()).1.render_fmt(120, f)?;
        Ok(())
    }
}

pub const ALLOC: BoxAllocator = BoxAllocator;

pub fn render_decls<'a, W: Write>(
    decls: impl IntoIterator<Item = &'a Decl>,
    out: &mut W,
) -> std::io::Result<()> {
    let mut scope = Why3Scope::new();
    scope.open();
    pretty_blocks(decls, &ALLOC, &mut scope).1.render(120, out)
}

pub fn render_module<W: Write>(module: &Module, out: &mut W) -> std::io::Result<()> {
    let mut scope = Why3Scope::new();
    module.pretty(&ALLOC, &mut scope).1.render(120, out)
}

/// To pretty print Why3 code, we keep track of what `Ident` are in scope in order to
/// assign them the simplest identifier based on their `name`: `name`, `name'0`, `name'1`...
struct Scope {
    /// Mapping from in-scope binders to symbols as they are going to appear in the printed Why3 code.
    rename: HashMap<Ident, Symbol>,
    /// Symbols in scope, which should be avoided by future binders.
    bound: HashSet<Symbol>,
    /// Stack of undo operations to apply when a chunk of binders go out of scope.
    ///
    /// Remark 1: This stack structure requires some acrobatics to do the correct thing sometimes.
    /// For example to deal with with non-recursive bindings:
    ///
    /// ```ignore
    /// let x1 = e1 in e2
    /// ```
    ///
    /// `x1` is in scope in `e2` but not `e1`.
    ///
    /// 1. render `e1` using the surrounding scope;
    /// 2. push the binding of `x1` with its name to be printed onto the scope stack;
    /// 3. render `e2` with that extended scope;
    /// 4. stitch together all of the produced `Doc`s and pop `x1` out of scope.
    ///
    /// Remark 2: If there were no shadowing, this field could be simplified to have type `Vec<Vec<Ident>>`.
    /// Unfortunately, `creusot::backend::logic::vcgen` currently generates code with shadowing
    /// to deal with recursive logic functions:
    ///
    /// ```ignore
    /// #[logic]
    /// #[ensures(POST(result))]
    /// fn f(x: usize) {
    ///   if x > 0 {
    ///     f(x - 1)
    ///   }
    /// }
    /// ```
    ///
    /// generates
    ///
    /// ```ignore
    /// constant x: usize
    /// function f (x: usize): ()    (* x is shadowed here (also unused) *)
    /// goal vc_f: ... POST(f(x-1)) -> POST(...)
    /// ```
    ///
    /// I don't know if it's the only place to fix; we can probably avoid shadowing if we really want to.
    undo: Vec<Vec<(Ident, Option<Symbol>)>>,
}

impl Scope {
    fn new() -> Self {
        Scope { bound: HashSet::new(), rename: HashMap::new(), undo: vec![] }
    }

    /// Open a scope: create a new chunk of binders that will go out of scope
    /// at the same time by a corresponding call to `close()`.
    fn open(&mut self) {
        self.undo.push(Vec::new());
    }

    /// Close the scope at the top of the stack, removing the chunk of binders that it contains.
    fn close(&mut self) {
        let undo = self.undo.pop().unwrap();
        for (ident, old) in undo.into_iter().rev() {
            let sym = match old {
                None => self.rename.remove(&ident).unwrap(),
                Some(old) => self.rename.insert(ident, old).unwrap(),
            };
            self.bound.remove(&sym);
        }
    }

    /// Bind an identifier in the current scope, assigning it a fresh symbol.
    fn bind(&mut self, ident: Ident) {
        let mut sym = ident.name.to_identifier();
        let name = sym.to_string();
        for i in 0.. {
            if !self.bound.contains(&sym) {
                break;
            }
            sym = Symbol::intern(&format!("{name}'{i}"));
        }
        self.bound.insert(sym);
        let old = self.rename.insert(ident, sym);
        self.undo.last_mut().unwrap().push((ident, old));
        return;
    }

    /// Get the symbol associated with an identifier in the current scope by a previous call to `bind()`.
    fn get(&self, ident: Ident) -> String {
        match self.rename.get(&ident) {
            Some(sym) => sym.to_string(),
            None => "ERROR_UNBOUND_".to_string() + &ident.name.to_string(), // TODO Output error message
        }
    }
}

/// Three separate scopes for values, types, and spans.
pub struct Why3Scope {
    value_scope: Scope,
    type_scope: Scope,
    span_scope: Scope,
}

impl Why3Scope {
    pub fn new() -> Self {
        Why3Scope { value_scope: Scope::new(), type_scope: Scope::new(), span_scope: Scope::new() }
    }

    pub fn open(&mut self) {
        self.value_scope.open();
        self.type_scope.open();
        self.span_scope.open();
    }

    pub fn close(&mut self) {
        self.value_scope.close();
        self.type_scope.close();
        self.span_scope.close();
    }

    pub fn bind_value(&mut self, ident: Ident) {
        self.value_scope.bind(ident)
    }

    pub fn bind_type(&mut self, ident: Ident) {
        self.type_scope.bind(ident)
    }

    pub fn bind_span(&mut self, ident: Ident) {
        self.span_scope.bind(ident)
    }

    pub fn get_value(&self, ident: Ident) -> String {
        self.value_scope.get(ident)
    }

    pub fn get_type(&self, ident: Ident) -> String {
        self.type_scope.get(ident)
    }

    pub fn get_span(&self, ident: Ident) -> String {
        self.span_scope.get(ident)
    }
}

pub trait Print {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone;

    fn display(&self) -> PrintDisplay<'_, Self>
    where
        Self: Sized,
    {
        PrintDisplay(self)
    }
}

/// We don't implement `Pretty` for `Ident` because we must be explicit about whether to use the scope for values, types, or spans.
impl Ident {
    pub fn pretty_value_name<'a, A: DocAllocator<'a>>(
        self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(scope.get_value(self))
    }

    pub fn pretty_type_name<'a, A: DocAllocator<'a>>(
        self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(scope.get_type(self))
    }

    pub fn pretty_span_name<'a, A: DocAllocator<'a>>(
        self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(scope.get_span(self))
    }
}

// TODO: replace with functions
macro_rules! parens {
    ($alloc:ident, $scope:ident, $parent:ident, $child:ident) => {
        parens($alloc, $scope, $parent.precedence(), $child)
    };
    ($alloc:ident, $scope:ident, $par_prec:expr, $child:ident) => {
        parens($alloc, $scope, $par_prec, $child)
    };
}

fn parens<'a, A: DocAllocator<'a>>(
    alloc: &'a A,
    scope: &mut Why3Scope,
    prec: Precedence,
    child: &'a Exp,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    let child_prec = child.precedence();
    if child_prec == Precedence::Atom {
        child.pretty(alloc, scope)
    } else if child_prec < prec {
        child.pretty(alloc, scope).parens()
    } else if child_prec == prec && child.associativity() != child.associativity() {
        child.pretty(alloc, scope).parens()
    } else {
        child.pretty(alloc, scope)
    }
}

macro_rules! ty_parens {
    ($alloc:ident, $scope:ident, $e:ident) => {
        if $e.complex() { $e.pretty($alloc, $scope).parens() } else { $e.pretty($alloc, $scope) }
    };
}

impl Print for Span {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_span(self.name);
        docs![
            alloc,
            "let%span",
            alloc.space(),
            self.name.pretty_span_name(alloc, scope),
            alloc.space(),
            alloc.text("="),
            alloc.space(),
            alloc.text(&self.path).double_quotes(),
            alloc.space(),
            alloc.as_string(self.start_line),
            alloc.space(),
            alloc.as_string(self.start_column),
            alloc.space(),
            alloc.as_string(self.end_line),
            alloc.space(),
            alloc.as_string(self.end_column),
        ]
    }
}

impl Print for Decl {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Decl::LogicDefn(log) => log.pretty(alloc, scope),
            Decl::PredDecl(p) => p.pretty(alloc, scope),
            Decl::TyDecl(t) => t.pretty(alloc, scope),
            Decl::LogicDecl(v) => v.pretty(alloc, scope),
            Decl::UseDecls(uses) => {
                alloc.intersperse(uses.iter().map(|u| u.pretty(alloc, scope)), alloc.hardline())
            }
            Decl::Axiom(a) => a.pretty(alloc, scope),
            Decl::Goal(g) => g.pretty(alloc, scope),
            Decl::ConstantDecl(c) => c.pretty(alloc, scope),
            Decl::Coma(d) => d.pretty(alloc, scope),
            Decl::LetSpans(spans) => alloc
                .intersperse(spans.iter().map(|span| span.pretty(alloc, scope)), alloc.hardline()),
            Decl::Meta(meta) => meta.pretty(alloc, scope),
            Decl::Comment(c) => alloc.text("(* ").append(c).append(" *)"),
        }
    }
}

impl Print for Module {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.open();
        let doc = alloc
            .text("module ")
            .append(self.name.to_string())
            .append(if self.attrs.is_empty() {
                alloc.nil()
            } else {
                alloc.concat(
                    self.attrs.iter().map(|attr| alloc.space().append(attr.pretty(alloc, scope))),
                )
            })
            .append(match self.meta.as_ref() {
                Some(meta) => alloc.text(" (* ").append(meta.pretty(alloc)).append(" *)"),
                None => alloc.nil(),
            })
            .append(alloc.hardline())
            .append(pretty_blocks(&self.decls, alloc, scope).indent(2))
            .append(alloc.hardline())
            .append("end");
        scope.close();
        doc
    }
}

// Items separated by empty lines
pub fn pretty_blocks<'a, T: Print + 'a, A: DocAllocator<'a>>(
    items: impl IntoIterator<Item = &'a T>,
    alloc: &'a A,
    scope: &mut Why3Scope,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    alloc.intersperse(
        items.into_iter().map(|item| item.pretty(alloc, scope)),
        alloc.hardline().append(alloc.hardline()),
    )
}

impl Print for Axiom {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.name);
        alloc
            .text("axiom ")
            .append(self.name.pretty_value_name(alloc, scope))
            .append(if self.rewrite { " [@rewrite]: " } else { ": " })
            .append(self.axiom.pretty(alloc, scope))
    }
}

impl Print for Goal {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.name);
        alloc
            .text("goal ")
            .append(self.name.pretty_value_name(alloc, scope))
            .append(": ")
            .append(self.goal.pretty(alloc, scope))
    }
}

impl Print for declaration::Constant {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.name);
        scope.open();
        let doc = docs![
            alloc,
            "constant ",
            self.name.pretty_value_name(alloc, scope),
            ": ",
            self.type_.pretty(alloc, scope),
            match &self.body {
                Some(b) => alloc.text(" = ").append(b.pretty(alloc, scope)),
                None => alloc.nil(),
            }
        ];
        scope.close();
        doc
    }
}

impl Print for Attribute {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match &self {
            Attribute::Attr(s) => alloc.text("@").append(s),
            Attribute::NamedSpan(s) => alloc.text("%#").append(s.pretty_span_name(alloc, scope)),
            Attribute::Span(f, ls, cs, le, ce) => alloc
                .text("#")
                .append(alloc.text(f).double_quotes())
                .append(alloc.space())
                .append(alloc.as_string(ls))
                .append(alloc.space())
                .append(alloc.as_string(cs))
                .append(alloc.space())
                .append(alloc.as_string(le))
                .append(alloc.space())
                .append(alloc.as_string(ce)),
        }
        .brackets()
    }
}

impl Print for Signature {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        // Assume that self.name is bound and that a local scope has been open for the parameters.
        // We bind the parameters here so they are in scope when printing the body of a Predicate.
        self.name
            .pretty_value_name(alloc, scope)
            .append(alloc.space())
            .append(alloc.intersperse(
                self.attrs.iter().map(|a| a.pretty(alloc, scope)).chain(once(alloc.nil())),
                alloc.space(),
            ))
            .append(arg_list(alloc, &self.args, scope))
            .append(
                self.retty.as_ref().map_or_else(
                    || alloc.nil(),
                    |t| alloc.text(" : ").append(t.pretty(alloc, scope)),
                ),
            )
            .append(alloc.line_().append(self.contract.pretty(alloc, scope)))
            .nest(2)
            .group()
    }
}

impl Print for Predicate {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.sig.name);
        scope.open();
        let doc = alloc
            .text("predicate ")
            .append(self.sig.pretty(alloc, scope).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, scope).indent(2));
        scope.close();
        doc
    }
}

fn arg_list<'b: 'a, 'a, A: DocAllocator<'a>>(
    alloc: &'a A,
    args: &'a [(Ident, Type)],
    scope: &mut Why3Scope,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    alloc.intersperse(args.iter().map(|b| pretty_binder(b, alloc, scope)), alloc.space())
}

fn pretty_binder<'a, A: DocAllocator<'a>>(
    (id, ty): &'a (Ident, Type),
    alloc: &'a A,
    scope: &mut Why3Scope,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    scope.bind_value(*id);
    id.pretty_value_name(alloc, scope).append(": ").append(ty.pretty(alloc, scope)).parens()
}

impl Print for LogicDefn {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        scope.bind_value(self.sig.name);
        scope.open();
        let doc = alloc
            .text("function ")
            .append(self.sig.pretty(alloc, scope).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, scope).indent(2));
        scope.close();
        doc
    }
}

impl Print for Use {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("use ")
            .append(if self.export { alloc.text("export ") } else { alloc.nil() })
            .append(alloc.intersperse(self.name.iter().map(|t| alloc.text(t.to_string())), "."))
    }
}

impl Print for Meta {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text("meta ").append(self.name.pretty(alloc, scope)).append(alloc.space()).append(
            alloc.intersperse(self.args.iter().map(|a| a.pretty(alloc, scope)), alloc.space()),
        )
    }
}

impl Print for MetaIdent {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            MetaIdent::Ident(i) => i.pretty(alloc, scope),
            MetaIdent::String(s) => alloc.text(format!("{s:?}")),
        }
    }
}

impl Print for MetaArg {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            MetaArg::Integer(i) => alloc.as_string(i),
            MetaArg::String(s) => alloc.text(format!("{s:?}")),
        }
    }
}

impl Print for LogicDecl {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let doc = match self.kind {
            Some(DeclKind::Function) => alloc.text("function "),
            Some(DeclKind::Predicate) => alloc.text("predicate "),
            Some(DeclKind::Constant) => alloc.text("constant "),
            None => alloc.nil(),
        };
        scope.bind_value(self.sig.name);
        scope.open();
        let doc = doc.append(self.sig.pretty(alloc, scope));
        scope.close();
        doc
    }
}

impl Print for Contract {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut doc = alloc.nil();

        for req in &self.requires {
            doc = doc.append(
                alloc
                    .text("requires ")
                    .append(req.exp.pretty(alloc, scope).braces())
                    .append(alloc.hardline()),
            )
        }

        for req in &self.ensures {
            doc = doc.append(
                alloc
                    .text("ensures ")
                    .append(
                        alloc
                            .space()
                            .append(req.exp.pretty(alloc, scope))
                            .append(alloc.space())
                            .braces(),
                    )
                    .append(alloc.hardline()),
            )
        }

        if let Some(ref var) = self.variant {
            doc = doc.append(
                alloc
                    .text("variant ")
                    .append(var.pretty(alloc, scope).braces())
                    .append(alloc.hardline()),
            )
        }

        doc
    }
}

impl Print for Type {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use Type::*;
        match self {
            TVar(v) => v.pretty_type_name(alloc, scope),
            TConstructor(ty) => ty.pretty_type_name(alloc, scope),
            TFun(a, b) => {
                ty_parens!(alloc, scope, a).append(" -> ").append(ty_parens!(alloc, scope, b))
            }
            TApp(tyf, args) => {
                if args.is_empty() {
                    tyf.pretty(alloc, scope)
                } else {
                    tyf.pretty(alloc, scope).append(alloc.space()).append(alloc.intersperse(
                        args.iter().map(|arg| ty_parens!(alloc, scope, arg)),
                        alloc.space(),
                    ))
                }
            }
            Tuple(tys) if tys.len() == 1 => tys[0].pretty(alloc, scope),
            Tuple(tys) => {
                alloc.intersperse(tys.iter().map(|ty| ty.pretty(alloc, scope)), ", ").parens()
            }
        }
    }
}

impl Print for Trigger {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.intersperse(self.0.iter().map(|t| t.pretty(alloc, scope)), ", ")
    }
}

impl Print for Exp {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            // TODO parenthesization
            Exp::Let { pattern, arg, body } => {
                scope.open();
                let arg = arg.pretty(alloc, scope);
                let doc = alloc
                    .text("let ")
                    .append(pattern.pretty(alloc, scope))
                    .append(" = ")
                    .append(arg)
                    .append(" in ")
                    .append(body.pretty(alloc, scope));
                scope.close();
                doc
            }
            Exp::Var(v) => v.pretty_value_name(alloc, scope),
            Exp::RecField { record, label } => {
                parens!(alloc, scope, self.precedence().next(), record)
                    .append(".")
                    .append(label.pretty_value_name(alloc, scope))
            }

            Exp::Tuple(args) => alloc
                .intersperse(args.iter().map(|a| parens!(alloc, scope, Precedence::Cast, a)), ", ")
                .parens(),

            Exp::Constructor { ctor, args } => {
                ctor.pretty_value_name(alloc, scope).append(if args.is_empty() {
                    alloc.nil()
                } else {
                    alloc.space().append(alloc.intersperse(
                        args.iter().map(|a| parens!(alloc, scope, Precedence::Brackets, a)),
                        " ",
                    ))
                })
            }
            Exp::FunLiteral(exps) => alloc
                .intersperse(exps.iter().map(|e| parens!(alloc, scope, Precedence::IfLet, e)), ";")
                .enclose("[|", "|]"),
            Exp::Const(c) => c.pretty(alloc, scope),

            Exp::UnaryOp(UnOp::Not, op) => {
                alloc.text("not ").append(parens!(alloc, scope, self, op))
            }

            Exp::UnaryOp(UnOp::Neg, op) => alloc.text("- ").append(parens!(alloc, scope, self, op)),
            Exp::UnaryOp(UnOp::FloatNeg, op) => {
                alloc.text(".- ").append(parens!(alloc, scope, self, op))
            }
            Exp::BinaryOp(op, l, r) => match self.associativity() {
                Some(AssocDir::Left) => parens!(alloc, scope, self, l),
                Some(AssocDir::Right) | None => parens!(alloc, scope, self.precedence().next(), l),
            }
            .append(alloc.line())
            .append(bin_op_to_string(op))
            .append(alloc.space())
            .append(match self.associativity() {
                Some(AssocDir::Right) => parens!(alloc, scope, self, r),
                Some(AssocDir::Left) | None => parens!(alloc, scope, self.precedence().next(), r),
            })
            .group(),
            Exp::Call(fun, args) => {
                parens!(alloc, scope, self, fun).append(alloc.space()).append(alloc.intersperse(
                    args.iter().map(|a| parens!(alloc, scope, Precedence::App.next(), a)),
                    alloc.space(),
                ))
            }

            Exp::Attr(attr, e) => {
                attr.pretty(alloc, scope).append(alloc.space()).append(e.pretty(alloc, scope))
            }
            Exp::Lam(binders, body) => {
                scope.open();
                let doc =
                    alloc
                        .text("fun ")
                        .append(alloc.intersperse(
                            binders.iter().map(|b| b.pretty(alloc, scope)),
                            alloc.space(),
                        ))
                        .append(" -> ")
                        .append(body.pretty(alloc, scope));
                scope.close();
                doc
            }

            Exp::Match(scrut, brs) => alloc
                .text("match ")
                .append(scrut.pretty(alloc, scope))
                .append(" with")
                .append(alloc.hardline())
                .append(
                    sep_end_by(
                        alloc,
                        brs.iter().map(|(pat, br)| {
                            scope.open();
                            let doc = alloc
                                .text("| ")
                                .append(pat.pretty(alloc, scope))
                                .append(" -> ")
                                .append(br.pretty(alloc, scope));
                            scope.close();
                            doc
                        }),
                        alloc.hardline(),
                    )
                    .append("end")
                    .indent(2),
                ),
            Exp::IfThenElse(s, i, e) => alloc
                .text("if ")
                .append(s.pretty(alloc, scope))
                .append(" then")
                .append(alloc.line().append(i.pretty(alloc, scope)).nest(2).append(alloc.line()))
                .append("else")
                .append(alloc.line().append(e.pretty(alloc, scope)).nest(2).append(alloc.line_()))
                .group(),
            Exp::Forall(binders, trig, exp) => {
                scope.open();
                let mut res = alloc.text("forall ").append(alloc.intersperse(
                    binders.iter().map(|(b, t)| {
                        scope.bind_value(*b);
                        b.pretty_value_name(alloc, scope)
                            .append(": ")
                            .append(t.pretty(alloc, scope))
                    }),
                    ", ",
                ));

                if trig.iter().any(|t| !t.0.is_empty()) {
                    res = res
                        .append(" [")
                        .append(
                            alloc.intersperse(trig.iter().map(|t| t.pretty(alloc, scope)), " | "),
                        )
                        .append("]");
                }

                let doc = res.append(". ").append(exp.pretty(alloc, scope));
                scope.close();
                doc
            }
            Exp::Exists(binders, trig, exp) => {
                scope.open();
                let mut res = alloc.text("exists ").append(alloc.intersperse(
                    binders.iter().map(|(b, t)| {
                        scope.bind_value(*b);
                        b.pretty_value_name(alloc, scope)
                            .append(": ")
                            .append(t.pretty(alloc, scope))
                    }),
                    ", ",
                ));

                if trig.iter().any(|t| !t.0.is_empty()) {
                    res = res
                        .append(" [")
                        .append(
                            alloc.intersperse(trig.iter().map(|t| t.pretty(alloc, scope)), " | "),
                        )
                        .append("]");
                }

                let doc = res.append(". ").append(exp.pretty(alloc, scope));
                scope.close();
                doc
            }
            Exp::Impl(hyp, exp) => {
                let hyp = parens!(alloc, scope, self, hyp);
                let impl_ = alloc
                    .line()
                    .append(alloc.text(" -> "))
                    .append(parens!(alloc, scope, self, exp))
                    .group();

                hyp.append(impl_)
            }
            Exp::Ascribe(e, t) => {
                parens!(alloc, scope, self, e).append(": ").append(t.pretty(alloc, scope)).group()
            }
            Exp::RecUp { record, updates } => {
                alloc
                    .space()
                    .append(parens!(alloc, scope, self.precedence().next(), record))
                    .append(" with ")
                    .append(
                        alloc
                            .intersperse(
                                updates.iter().map(|(nm, a)| {
                                    nm.pretty_value_name(alloc, scope)
                                        .append(" = ")
                                        .append(parens!(alloc, scope, Precedence::Attr.next(), a))
                                }),
                                alloc.text(";").append(alloc.line()),
                            )
                            .align(),
                    )
                    .append(alloc.space())
                    .braces()
                    .group()
            }
            Exp::Record { fields } => {
                alloc
                    .space()
                    .append(
                        alloc
                            .intersperse(
                                fields.iter().map(|(nm, a)| {
                                    nm.pretty_value_name(alloc, scope)
                                        .append(" = ")
                                        .append(parens!(alloc, scope, Precedence::Attr.next(), a))
                                }),
                                alloc.text(";").append(alloc.line()),
                            )
                            .align(),
                    )
                    .append(alloc.space())
                    .braces()
                    .group()
            }
        }
    }
}

impl Print for Binder {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Binder::Wild => alloc.text("_"),
            Binder::UnNamed(ty) => ty.pretty(alloc, scope),
            Binder::Named(id) => {
                scope.bind_value(*id);
                id.pretty_value_name(alloc, scope)
            }
            Binder::Typed(ghost, ids, ty) => {
                (if *ghost { alloc.text("ghost ") } else { alloc.nil() })
                    .append(
                        alloc
                            .intersperse(
                                ids.iter().map(|id| match id {
                                    None => alloc.text("_"),
                                    Some(id) => {
                                        scope.bind_value(*id);
                                        id.pretty_value_name(alloc, scope)
                                    }
                                }),
                                alloc.space(),
                            )
                            .append(": ")
                            .append(ty.pretty(alloc, scope)),
                    )
                    .parens()
            }
        }
    }
}

impl Print for Pattern {
    fn pretty<'a, A: DocAllocator<'a, Doc: Clone>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A> {
        fn pretty_rec<'a, A: DocAllocator<'a, Doc: Clone>>(
            p: &'a Pattern,
            alloc: &'a A,
            scope: &mut Why3Scope,
            seen: &mut HashSet<Ident>,
        ) -> DocBuilder<'a, A> {
            match p {
                Pattern::Wildcard => alloc.text("_"),
                Pattern::VarP(v) => {
                    if !seen.contains(v) {
                        scope.bind_value(*v);
                        seen.insert(*v);
                    }
                    v.pretty_value_name(alloc, scope)
                }
                Pattern::TupleP(pats) => alloc
                    .intersperse(pats.iter().map(|p| pretty_rec(p, alloc, scope, seen)), ", ")
                    .parens(),
                Pattern::ConsP(c, pats) => {
                    let mut doc = c.pretty_value_name(alloc, scope);

                    if !pats.is_empty() {
                        doc = doc.append(alloc.space()).append(alloc.intersperse(
                            pats.iter().map(|p| {
                                if matches!(p, Pattern::ConsP(_, _)) {
                                    pretty_rec(p, alloc, scope, seen).parens()
                                } else {
                                    pretty_rec(p, alloc, scope, seen)
                                }
                            }),
                            " ",
                        ))
                    }
                    doc
                }
                Pattern::RecP(pats) => {
                    let pats = pats.iter().map(|(field, pat)| {
                        field
                            .pretty_value_name(alloc, scope)
                            .append(" = ")
                            .append(pretty_rec(pat, alloc, scope, seen))
                    });

                    alloc.intersperse(pats, " ; ").braces()
                }
                Pattern::OrP(pats) => {
                    alloc.intersperse(pats.iter().map(|p| pretty_rec(p, alloc, scope, seen)), " | ")
                }
            }
        }
        pretty_rec(self, alloc, scope, &mut HashSet::new())
    }
}

impl Name {
    pub fn pretty_value_name<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Name::Local(i, None) => i.pretty_value_name(alloc, scope),
            Name::Local(i, Some(s)) => i.pretty_value_name(alloc, scope).append(s.to_string()),
            Name::Global(q) => q.pretty(alloc, scope),
        }
    }

    pub fn pretty_type_name<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Name::Local(i, None) => i.pretty_type_name(alloc, scope),
            Name::Local(i, Some(s)) => i.pretty_type_name(alloc, scope).append(s.to_string()),
            Name::Global(q) => q.pretty(alloc, scope),
        }
    }
}

fn sep_end_by<'a, A, D, I, S>(alloc: &'a D, docs: I, separator: S) -> DocBuilder<'a, D, A>
where
    D: DocAllocator<'a, A>,
    I: IntoIterator,
    I::Item: Pretty<'a, D, A>,
    S: Pretty<'a, D, A> + Clone,
{
    let mut result = alloc.nil();
    let iter = docs.into_iter();

    for doc in iter {
        result = result.append(doc);
        result = result.append(separator.clone());
    }

    result
}

fn bin_op_to_string(op: &BinOp) -> &str {
    use BinOp::*;
    match op {
        LogAnd => "/\\",
        LazyAnd => "&&",
        LogOr => "\\/",
        LazyOr => "||",
        Add => "+",
        Sub => "-",
        Mul => "*",
        Div => "/",
        Mod => "%",
        Eq => "=",
        Ne => "<>",
        Gt => ">",
        Ge => ">=",
        Lt => "<",
        Le => "<=",
        FloatAdd => ".+",
        FloatSub => ".-",
        FloatMul => ".*",
        FloatDiv => "./",
        FloatEq => ".=",
        FloatLt => ".<",
        FloatLe => ".<=",
        FloatGt => ".>",
        FloatGe => ".>=",
    }
}

impl Print for Constant {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Constant::Other(o) => alloc.text(o),
            Constant::Bool(b) => {
                if *b {
                    alloc.text("true")
                } else {
                    alloc.text("false")
                }
            }
            Constant::Char(c, t) => {
                let c = *c as u32;
                alloc.as_string(c).append(": ").append(t.pretty(alloc, scope)).parens()
            }
            Constant::Int(i, Some(t)) => {
                alloc.as_string(i).append(": ").append(t.pretty(alloc, scope)).parens()
            }
            Constant::Int(i, None) => alloc.as_string(i),
            Constant::Uint(i, Some(t)) => {
                alloc.as_string(i).append(": ").append(t.pretty(alloc, scope)).parens()
            }
            Constant::String(s) => alloc.text(format!("{s:?}")),
            Constant::Uint(i, None) => alloc.as_string(i),
            Constant::Float(f, None) => {
                assert!(f.is_finite());
                let mut doc = alloc.text(print_float(*f));
                if f.is_sign_negative() {
                    doc = doc.parens();
                }
                doc
            }
            Constant::Float(f, Some(t)) => {
                assert!(f.is_finite());
                let f_str = print_float(*f);
                alloc.text(f_str).append(": ").append(t.pretty(alloc, scope)).parens()
            }
        }
    }
}

fn print_float(f: f64) -> String {
    if f.fract() != 0.0 {
        let (mantissa, exp, _) = f.integer_decode();
        let leading = if f.is_subnormal() { "0" } else { "1" };

        format!(
            "{}0x{}.{:012x}p{}",
            if f.is_sign_negative() { "-" } else { "" },
            leading,
            mantissa & !(1 << 52),
            exp + 52
        )
    } else {
        format!("{}{f}.0", if f.is_sign_negative() && f.is_zero() { "-" } else { "" })
    }
}

impl Print for TyDecl {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let ty_decl = match self {
            TyDecl::Opaque { ty_name, ty_params } => {
                scope.bind_type(*ty_name);
                scope.open();
                let mut decl = alloc.text("type ").append(ty_name.pretty_type_name(alloc, scope));
                if !ty_params.is_empty() {
                    decl = decl.append(" ").append(alloc.intersperse(
                        ty_params.iter().map(|p| {
                            scope.bind_type(*p);
                            alloc.text("'").append(p.pretty_type_name(alloc, scope))
                        }),
                        alloc.space(),
                    ));
                }
                scope.close();
                decl
            }
            TyDecl::Alias { ty_name, ty_params, alias } => {
                scope.bind_type(*ty_name);
                scope.open();
                let doc = alloc
                    .text("type ")
                    .append(ty_name.pretty_type_name(alloc, scope))
                    .append(" ")
                    .append(alloc.intersperse(
                        ty_params.iter().map(|p| {
                            scope.bind_type(*p);
                            alloc.text("'").append(p.pretty_type_name(alloc, scope))
                        }),
                        alloc.space(),
                    ))
                    .append(alloc.text(" =").append(alloc.hardline()))
                    .append(alias.pretty(alloc, scope).indent(2));
                scope.close();
                doc
            }
            TyDecl::Adt { tys } => {
                // First bind all type and constructor names (i.e., pick concrete unused strings as their names)
                // in the current scope. When printing the type definition, we open a local scope to bind the type variables.
                for AdtDecl { ty_name, sumrecord, .. } in tys.iter() {
                    scope.bind_type(*ty_name);
                    match sumrecord {
                        SumRecord::Sum(constrs) => {
                            for ConstructorDecl { name, .. } in constrs.iter() {
                                scope.bind_value(*name);
                            }
                        }
                        SumRecord::Record(fields) => {
                            for FieldDecl { name, .. } in fields.iter() {
                                scope.bind_value(*name);
                            }
                        }
                    }
                }
                scope.open();
                let header = once("type").chain(repeat("with"));
                let mut decls = Vec::new();
                for (hdr, AdtDecl { ty_name, ty_params, sumrecord }) in header.zip(tys.iter()) {
                    let decl = alloc
                        .nil()
                        .append(hdr)
                        .append(" ")
                        .append(ty_name.pretty_type_name(alloc, scope))
                        .append(" ")
                        .append(alloc.intersperse(
                            ty_params.iter().map(|p| {
                                scope.bind_type(*p);
                                alloc.text("'").append(p.pretty_type_name(alloc, scope))
                            }),
                            alloc.space(),
                        ));
                    let inner_doc = match sumrecord {
                        SumRecord::Sum(constrs) => alloc.intersperse(
                            constrs
                                .iter()
                                .map(|cons| alloc.text("| ").append(cons.pretty(alloc, scope))),
                            alloc.hardline(),
                        ),
                        SumRecord::Record(fields) => alloc
                            .nil()
                            .append(alloc.space())
                            .append(
                                alloc
                                    .intersperse(
                                        fields.iter().map(|f| f.pretty(alloc, scope)),
                                        alloc.text(";").append(alloc.line()),
                                    )
                                    .align(),
                            )
                            .append(alloc.space())
                            .braces()
                            .group(),
                    };

                    let decl = decl
                        .append(alloc.text(" =").append(alloc.hardline()))
                        .append(inner_doc.indent(2));
                    decls.push(decl);
                }
                scope.close();
                alloc.intersperse(decls, alloc.hardline())
            }
        };

        ty_decl
    }
}

impl Print for ConstructorDecl {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut cons_doc = self.name.pretty_value_name(alloc, scope);

        if !self.fields.is_empty() {
            cons_doc = cons_doc.append(alloc.space()).append(alloc.intersperse(
                self.fields.iter().map(|ty_arg| ty_parens!(alloc, scope, ty_arg)),
                " ",
            ));
        }

        cons_doc
    }
}

impl Print for FieldDecl {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        self.name
            .pretty_value_name(alloc, scope)
            .append(alloc.text(": "))
            .append(self.ty.pretty(alloc, scope))
    }
}

impl Print for Symbol {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(self.to_string())
    }
}

impl Print for QName {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let module_path = self.module.iter().map(|t| alloc.text(t.to_string()));
        alloc.intersperse(module_path.chain([alloc.text(self.name.to_string())]), ".")
    }
}
