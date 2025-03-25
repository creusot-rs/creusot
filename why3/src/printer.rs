use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    iter::{once, repeat},
};

use crate::{
    Exp, Ident, IdentString, QName,
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
use string_interner::DefaultSymbol;

pub struct PrintDisplay<'a, A: Print>(&'a A);

impl<'a, A: Print> Display for PrintDisplay<'a, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = BoxAllocator;
        self.0.pretty(&alloc, &mut Why3Scope::new()).1.render_fmt(120, f)?;
        Ok(())
    }
}

pub const ALLOC: BoxAllocator = BoxAllocator;

struct Scope {
    bound: HashSet<DefaultSymbol>,
    rename: HashMap<Ident, DefaultSymbol>,
    undo: Vec<Vec<Ident>>,
}

impl Scope {
    fn new() -> Self {
        Scope { bound: HashSet::new(), rename: HashMap::new(), undo: vec![Vec::new()] }
    }

    fn open(&mut self) {
        self.undo.push(Vec::new());
    }

    fn close(&mut self) {
        let undo = self.undo.pop().unwrap();
        for ident in undo {
            self.unbind(ident);
        }
    }

    fn bind(&mut self, ident: Ident) -> DefaultSymbol {
        if ident.id == 0 {
            return ident.name.0;
        }
        let name = ident.name.as_str();
        let mut sym = crate::name::INTERNER.write().unwrap().get_or_intern(&name);
        let mut i = 0;
        while self.bound.contains(&sym) {
            sym = crate::name::INTERNER.write().unwrap().get_or_intern(&format!("{name}'{i}"));
            i += 1;
        }
        self.bound.insert(sym);
        self.rename.insert(ident, sym);
        return sym;
    }

    fn get(&self, ident: Ident) -> DefaultSymbol {
        if ident.id == 0 { ident.name.0 } else { self.rename[&ident] }
    }

    fn unbind(&mut self, ident: Ident) {
        let sym = self.rename.remove(&ident).unwrap();
        self.bound.remove(&sym);
    }
}

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

    pub fn bind_value(&mut self, ident: Ident) -> DefaultSymbol {
        self.value_scope.bind(ident)
    }

    pub fn bind_type(&mut self, ident: Ident) -> DefaultSymbol {
        self.type_scope.bind(ident)
    }

    pub fn bind_span(&mut self, ident: Ident) -> DefaultSymbol {
        self.span_scope.bind(ident)
    }

    pub fn get_value(&self, ident: Ident) -> DefaultSymbol {
        self.value_scope.get(ident)
    }

    pub fn get_type(&self, ident: Ident) -> DefaultSymbol {
        self.type_scope.get(ident)
    }

    pub fn get_span(&self, ident: Ident) -> DefaultSymbol {
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

impl Ident {
    pub fn pretty_value_name<'a, A: DocAllocator<'a>>(
        self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let s = crate::INTERNER.read().unwrap().resolve(scope.get_value(self)).unwrap().to_string();
        alloc.text(s)
    }

    pub fn pretty_type_name<'a, A: DocAllocator<'a>>(
        self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let s = crate::INTERNER.read().unwrap().resolve(scope.get_type(self)).unwrap().to_string();
        alloc.text(s)
    }

    pub fn pretty_span_name<'a, A: DocAllocator<'a>>(
        self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let s = crate::INTERNER.read().unwrap().resolve(scope.get_span(self)).unwrap().to_string();
        alloc.text(s)
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
        let doc = alloc
            .text("module ")
            .append(self.name.as_str())
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
            .append(if self.rewrite { " [@rewrite] : " } else { " : " })
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
            .append(" : ")
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
        docs![
            alloc,
            "constant ",
            self.name.pretty_value_name(alloc, scope),
            " : ",
            self.type_.pretty(alloc, scope),
            match &self.body {
                Some(b) => alloc.text(" = ").append(b.pretty(alloc, scope)),
                None => alloc.nil(),
            }
        ]
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
        scope.bind_value(self.name);
        scope.open();
        let doc =
            self.name
                .pretty_value_name(alloc, scope)
                .append(alloc.space())
                .append(alloc.intersperse(
                    self.attrs.iter().map(|a| a.pretty(alloc, scope)).chain(once(alloc.nil())),
                    alloc.space(),
                ))
                .append(arg_list(alloc, &self.args, scope))
                .append(self.retty.as_ref().map_or_else(
                    || alloc.nil(),
                    |t| alloc.text(" : ").append(t.pretty(alloc, scope)),
                ))
                .append(alloc.line_().append(self.contract.pretty(alloc, scope)))
                .nest(2)
                .group();
        scope.close();
        doc
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
        alloc
            .text("predicate ")
            .append(self.sig.pretty(alloc, scope).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, scope).indent(2))
    }
}

fn arg_list<'b: 'a, 'a, A: DocAllocator<'a>>(
    alloc: &'a A,
    args: &'a [Binder],
    scope: &mut Why3Scope,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    alloc.intersperse(args.iter().map(|b| b.pretty(alloc, scope)), alloc.space())
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
        alloc
            .text("function ")
            .append(self.sig.pretty(alloc, scope).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, scope).indent(2))
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
            .append(alloc.intersperse(self.name.iter().map(|t| alloc.text(t.as_str())), "."))
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
        let mut doc = alloc.nil();

        match self.kind {
            Some(DeclKind::Function) => doc = doc.append("function "),
            Some(DeclKind::Predicate) => doc = doc.append("predicate "),
            Some(DeclKind::Constant) => doc = doc.append("constant "),
            None => {}
        };

        doc = doc.append(self.sig.pretty(alloc, scope));
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
            TVar(v) => alloc.text(format!("'{}", v.as_str())),
            TConstructor(ty) => ty.pretty(alloc, scope),
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
            Exp::QVar(v) => v.pretty(alloc, scope),
            Exp::RecField { record, label } => {
                parens!(alloc, scope, self.precedence().next(), record)
                    .append(".")
                    .append(label.as_str())
            }

            Exp::Tuple(args) => alloc
                .intersperse(args.iter().map(|a| parens!(alloc, scope, Precedence::Cast, a)), ", ")
                .parens(),

            Exp::Constructor { ctor, args } => {
                ctor.pretty(alloc, scope).append(if args.is_empty() {
                    alloc.nil()
                } else {
                    alloc.space().append(alloc.intersperse(
                        args.iter().map(|a| parens!(alloc, scope, Precedence::Brackets, a)),
                        " ",
                    ))
                })
            }
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
                            .append(" : ")
                            .append(t.pretty(alloc, scope))
                    }),
                    ", ",
                ));

                if trig.iter().fold(false, |acc, t| acc || !t.0.is_empty()) {
                    res = res
                        .append(" [")
                        .append(
                            alloc.intersperse(trig.iter().map(|t| t.pretty(alloc, scope)), " | "),
                        )
                        .append("]");
                }

                let doc = res.append(" . ").append(exp.pretty(alloc, scope));
                scope.close();
                doc
            }
            Exp::Exists(binders, trig, exp) => {
                scope.open();
                let mut res = alloc.text("exists ").append(alloc.intersperse(
                    binders.iter().map(|(b, t)| {
                        scope.bind_value(*b);
                        b.pretty_value_name(alloc, scope)
                            .append(" : ")
                            .append(t.pretty(alloc, scope))
                    }),
                    ", ",
                ));

                if trig.iter().fold(false, |acc, t| acc || !t.0.is_empty()) {
                    res = res
                        .append(" [")
                        .append(
                            alloc.intersperse(trig.iter().map(|t| t.pretty(alloc, scope)), " | "),
                        )
                        .append("]");
                }

                let doc = res.append(" . ").append(exp.pretty(alloc, scope));
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
                parens!(alloc, scope, self, e).append(" : ").append(t.pretty(alloc, scope)).group()
            }
            Exp::Old(e) => alloc.text("old").append(e.pretty(alloc, scope).parens()),
            Exp::RecUp { record, updates } => alloc
                .space()
                .append(parens!(alloc, scope, self.precedence().next(), record))
                .append(" with ")
                .append(
                    alloc
                        .intersperse(
                            updates.iter().map(|(nm, a)| {
                                alloc.text(nm.as_str()).append(" = ").append(parens!(
                                    alloc,
                                    scope,
                                    Precedence::Attr.next(),
                                    a
                                ))
                            }),
                            alloc.text(";").append(alloc.line()),
                        )
                        .align(),
                )
                .append(alloc.space())
                .braces()
                .group(),
            Exp::Record { fields } => alloc
                .space()
                .append(
                    alloc
                        .intersperse(
                            fields.iter().map(|(nm, a)| {
                                alloc.text(nm.as_str()).append(" = ").append(parens!(
                                    alloc,
                                    scope,
                                    Precedence::Attr.next(),
                                    a
                                ))
                            }),
                            alloc.text(";").append(alloc.line()),
                        )
                        .align(),
                )
                .append(alloc.space())
                .braces()
                .group(),
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
                                ids.iter().map(|id| id.pretty(alloc, scope)),
                                alloc.space(),
                            )
                            .append(" : ")
                            .append(ty.pretty(alloc, scope)),
                    )
                    .parens()
            }
        }
    }
}

impl Print for Pattern {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        scope: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Pattern::Wildcard => alloc.text("_"),
            Pattern::VarP(v) => {
                scope.bind_value(*v);
                v.pretty_value_name(alloc, scope)
            }
            Pattern::TupleP(pats) => {
                alloc.intersperse(pats.iter().map(|p| p.pretty(alloc, scope)), ", ").parens()
            }
            Pattern::ConsP(c, pats) => {
                let mut doc = c.pretty(alloc, scope);

                if !pats.is_empty() {
                    doc = doc.append(alloc.space()).append(alloc.intersperse(
                        pats.iter().map(|p| {
                            if matches!(p, Pattern::ConsP(_, _)) {
                                p.pretty(alloc, scope).parens()
                            } else {
                                p.pretty(alloc, scope)
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
                        .append(pat.pretty(alloc, scope))
                });

                alloc.intersperse(pats, " ; ").braces()
            }
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
        BitAnd => unreachable!("the & operator can't be instanced in infix notation"),
        BitOr => unreachable!("the | operator can't be instanced in infix notation"),
        BitXor => unreachable!("the ^ operator can't be instanced in infix notation"),
        Shl => unreachable!("the << operator can't be instanced in infix notation"),
        Shr => unreachable!("the >> operator can't be instanced in infix notation"),
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
                alloc.as_string(c).append(" : ").append(t.pretty(alloc, scope)).parens()
            }
            Constant::Int(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc, scope)).parens()
            }
            Constant::Int(i, None) => alloc.as_string(i),
            Constant::Uint(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc, scope)).parens()
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
                alloc.text(f_str).append(" : ").append(t.pretty(alloc, scope)).parens()
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

impl Print for IdentString {
    fn pretty<'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut Why3Scope,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(self.as_str())
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
        let module_path = self.module.iter().map(|t| alloc.text(t.as_str()));
        alloc.intersperse(module_path.chain([alloc.text(self.name.as_str())]), ".")
    }
}
