use std::{
    fmt::Display,
    iter::{once, repeat},
};

use crate::{
    Exp, Ident, QName,
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

impl<'a, A: Print> Display for PrintDisplay<'a, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = BoxAllocator;
        self.0.pretty(&alloc).1.render_fmt(120, f)?;
        Ok(())
    }
}

pub const ALLOC: BoxAllocator = BoxAllocator;

pub trait Print {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone;

    fn display(&self) -> PrintDisplay<'_, Self>
    where
        Self: Sized,
    {
        PrintDisplay(self)
    }
}

// TODO: replace with functions
macro_rules! parens {
    ($alloc:ident, $parent:ident, $child:ident) => {
        parens($alloc, $parent.precedence(), $child)
    };
    ($alloc:ident, $par_prec:expr, $child:ident) => {
        parens($alloc, $par_prec, $child)
    };
}

macro_rules! ty_parens {
    ($alloc:ident, $e:ident) => {
        if $e.complex() { $e.pretty($alloc).parens() } else { $e.pretty($alloc) }
    };
}

fn parens<'b, 'a: 'b, A: DocAllocator<'a>>(
    alloc: &'a A,
    prec: Precedence,
    child: &'a Exp,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    let child_prec = child.precedence();
    if child_prec == Precedence::Atom {
        child.pretty(alloc)
    } else if child_prec < prec {
        child.pretty(alloc).parens()
    } else if child_prec == prec && child.associativity() != child.associativity() {
        child.pretty(alloc).parens()
    } else {
        child.pretty(alloc)
    }
}

impl Print for Span {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        docs![
            alloc,
            "let%span",
            alloc.space(),
            self.name.pretty(alloc),
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Decl::LogicDefn(log) => log.pretty(alloc),
            Decl::PredDecl(p) => p.pretty(alloc),
            Decl::TyDecl(t) => t.pretty(alloc),
            Decl::LogicDecl(v) => v.pretty(alloc),
            Decl::UseDecls(uses) => {
                alloc.intersperse(uses.iter().map(|u| u.pretty(alloc)), alloc.hardline())
            }
            Decl::Axiom(a) => a.pretty(alloc),
            Decl::Goal(g) => g.pretty(alloc),
            Decl::ConstantDecl(c) => c.pretty(alloc),
            Decl::Coma(d) => d.pretty(alloc),
            Decl::LetSpans(spans) => {
                alloc.intersperse(spans.iter().map(|span| span.pretty(alloc)), alloc.hardline())
            }
            Decl::Meta(meta) => meta.pretty(alloc),
            Decl::Comment(c) => alloc.text("(* ").append(c).append(" *)"),
        }
    }
}

impl Print for Module {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let doc = alloc
            .text("module ")
            .append(&*self.name)
            .append(if self.attrs.is_empty() {
                alloc.nil()
            } else {
                alloc.concat(self.attrs.iter().map(|attr| alloc.space().append(attr.pretty(alloc))))
            })
            .append(match self.meta.as_ref() {
                Some(meta) => alloc.text(" (* ").append(meta.pretty(alloc)).append(" *)"),
                None => alloc.nil(),
            })
            .append(alloc.hardline())
            .append(pretty_blocks(&self.decls, alloc).indent(2))
            .append(alloc.hardline())
            .append("end");
        doc
    }
}

// Items separated by empty lines
pub fn pretty_blocks<'a, T: Print + 'a, A: DocAllocator<'a>>(
    items: impl IntoIterator<Item = &'a T>,
    alloc: &'a A,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    alloc.intersperse(
        items.into_iter().map(|item| item.pretty(alloc)),
        alloc.hardline().append(alloc.hardline()),
    )
}

impl Print for Axiom {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("axiom ")
            .append(self.name.pretty(alloc))
            .append(if self.rewrite { " [@rewrite] : " } else { " : " })
            .append(self.axiom.pretty(alloc))
    }
}

impl Print for Goal {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("goal ")
            .append(self.name.pretty(alloc))
            .append(" : ")
            .append(self.goal.pretty(alloc))
    }
}

impl Print for declaration::Constant {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        docs![
            alloc,
            "constant ",
            self.name.pretty(alloc),
            " : ",
            self.type_.pretty(alloc),
            match &self.body {
                Some(b) => alloc.text(" = ").append(b.pretty(alloc)),
                None => alloc.nil(),
            }
        ]
    }
}

impl Print for Attribute {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match &self {
            Attribute::Attr(s) => alloc.text("@").append(s),
            Attribute::NamedSpan(s) => alloc.text("%#").append(s),
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        self.name
            .pretty(alloc)
            .append(alloc.space())
            .append(alloc.intersperse(
                self.attrs.iter().map(|a| a.pretty(alloc)).chain(once(alloc.nil())),
                alloc.space(),
            ))
            .append(arg_list(alloc, &self.args))
            .append(
                self.retty
                    .as_ref()
                    .map_or_else(|| alloc.nil(), |t| alloc.text(" : ").append(t.pretty(alloc))),
            )
            .append(alloc.line_().append(self.contract.pretty(alloc)))
            .nest(2)
            .group()
        // .append(alloc.line())
        // .append(self.contract.pretty(alloc).indent(2))
    }
}

impl Print for Predicate {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("predicate ")
            .append(self.sig.pretty(alloc).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc).indent(2))
    }
}

fn arg_list<'b: 'a, 'a, A: DocAllocator<'a>>(alloc: &'a A, args: &'a [Binder]) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    alloc.intersperse(args.iter().map(|b| b.pretty(alloc)), alloc.space())
}

impl Print for LogicDefn {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("function ")
            .append(self.sig.pretty(alloc).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc).indent(2))
    }
}

impl Print for Use {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("use ")
            .append(if self.export { alloc.text("export ") } else { alloc.nil() })
            .append(alloc.intersperse(self.name.iter().map(|t| alloc.text(&t.0)), "."))
            .append(if let Some(as_) = &self.as_ {
                alloc.text(" as ").append(as_.pretty(alloc))
            } else {
                alloc.nil()
            })
    }
}

impl Print for Meta {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("meta ")
            .append(self.name.pretty(alloc))
            .append(alloc.space())
            .append(alloc.intersperse(self.args.iter().map(|a| a.pretty(alloc)), alloc.space()))
    }
}

impl Print for MetaIdent {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            MetaIdent::Ident(i) => i.pretty(alloc),
            MetaIdent::String(s) => alloc.text(format!("{s:?}")),
        }
    }
}

impl Print for MetaArg {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            MetaArg::Integer(i) => alloc.as_string(i),
        }
    }
}

impl Print for LogicDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
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

        doc = doc.append(self.sig.pretty(alloc));
        doc
    }
}

impl Print for Contract {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut doc = alloc.nil();

        for req in &self.requires {
            doc = doc.append(
                alloc
                    .text("requires ")
                    .append(req.exp.pretty(alloc).braces())
                    .append(alloc.hardline()),
            )
        }

        for req in &self.ensures {
            doc = doc.append(
                alloc
                    .text("ensures ")
                    .append(
                        alloc.space().append(req.exp.pretty(alloc)).append(alloc.space()).braces(),
                    )
                    .append(alloc.hardline()),
            )
        }

        if let Some(ref var) = self.variant {
            doc = doc.append(
                alloc.text("variant ").append(var.pretty(alloc).braces()).append(alloc.hardline()),
            )
        }

        doc
    }
}

impl Print for Type {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use Type::*;
        match self {
            TVar(v) => alloc.text(format!("'{}", v.0)),
            TConstructor(ty) => ty.pretty(alloc),
            TFun(a, b) => ty_parens!(alloc, a).append(" -> ").append(ty_parens!(alloc, b)),
            TApp(tyf, args) => {
                if args.is_empty() {
                    tyf.pretty(alloc)
                } else {
                    tyf.pretty(alloc).append(alloc.space()).append(
                        alloc.intersperse(
                            args.iter().map(|arg| ty_parens!(alloc, arg)),
                            alloc.space(),
                        ),
                    )
                }
            }
            Tuple(tys) if tys.len() == 1 => tys[0].pretty(alloc),
            Tuple(tys) => alloc.intersperse(tys.iter().map(|ty| ty.pretty(alloc)), ", ").parens(),
        }
    }
}

impl Print for Trigger {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.intersperse(self.0.iter().map(|t| t.pretty(alloc)), ", ")
    }
}

impl Print for Exp {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            // TODO parenthesization
            Exp::Let { pattern, arg, body } => alloc
                .text("let ")
                .append(pattern.pretty(alloc))
                .append(" = ")
                .append(arg.pretty(alloc))
                .append(" in ")
                .append(body.pretty(alloc)),
            Exp::Var(v) => v.pretty(alloc),
            Exp::QVar(v) => v.pretty(alloc),
            Exp::RecField { record, label } => {
                parens!(alloc, self.precedence().next(), record).append(".").append(label)
            }

            Exp::Tuple(args) => alloc
                .intersperse(args.iter().map(|a| parens!(alloc, Precedence::Cast, a)), ", ")
                .parens(),

            Exp::Constructor { ctor, args } => {
                ctor.pretty(alloc).append(if args.is_empty() {
                    alloc.nil()
                } else {
                    alloc.space().append(alloc.intersperse(
                        args.iter().map(|a| parens!(alloc, Precedence::Brackets, a)),
                        " ",
                    ))
                })
            }
            Exp::Const(c) => c.pretty(alloc),

            Exp::UnaryOp(UnOp::Not, op) => alloc.text("not ").append(parens!(alloc, self, op)),

            Exp::UnaryOp(UnOp::Neg, op) => alloc.text("- ").append(parens!(alloc, self, op)),
            Exp::UnaryOp(UnOp::FloatNeg, op) => alloc.text(".- ").append(parens!(alloc, self, op)),
            Exp::BinaryOp(op, l, r) => match self.associativity() {
                Some(AssocDir::Left) => parens!(alloc, self, l),
                Some(AssocDir::Right) | None => parens!(alloc, self.precedence().next(), l),
            }
            .append(alloc.line())
            .append(bin_op_to_string(op))
            .append(alloc.space())
            .append(match self.associativity() {
                Some(AssocDir::Right) => parens!(alloc, self, r),
                Some(AssocDir::Left) | None => parens!(alloc, self.precedence().next(), r),
            })
            .group(),
            Exp::Call(fun, args) => {
                parens!(alloc, self, fun).append(alloc.space()).append(alloc.intersperse(
                    args.iter().map(|a| parens!(alloc, Precedence::App.next(), a)),
                    alloc.space(),
                ))
            }

            Exp::Attr(attr, e) => attr.pretty(alloc).append(alloc.space()).append(e.pretty(alloc)),
            Exp::Abs(binders, body) => alloc
                .text("fun ")
                .append(alloc.intersperse(binders.iter().map(|b| b.pretty(alloc)), alloc.space()))
                .append(" -> ")
                .append(body.pretty(alloc)),

            Exp::Match(scrut, brs) => alloc
                .text("match ")
                .append(scrut.pretty(alloc))
                .append(" with")
                .append(alloc.hardline())
                .append(
                    sep_end_by(
                        alloc,
                        brs.iter().map(|(pat, br)| {
                            alloc
                                .text("| ")
                                .append(pat.pretty(alloc))
                                .append(" -> ")
                                .append(br.pretty(alloc))
                        }),
                        alloc.hardline(),
                    )
                    .append("end")
                    .indent(2),
                ),
            Exp::IfThenElse(s, i, e) => alloc
                .text("if ")
                .append(s.pretty(alloc))
                .append(" then")
                .append(alloc.line().append(i.pretty(alloc)).nest(2).append(alloc.line()))
                .append("else")
                .append(alloc.line().append(e.pretty(alloc)).nest(2).append(alloc.line_()))
                .group(),
            Exp::Forall(binders, trig, exp) => {
                let mut res = alloc.text("forall ").append(
                    alloc.intersperse(
                        binders
                            .iter()
                            .map(|(b, t)| b.pretty(alloc).append(" : ").append(t.pretty(alloc))),
                        ", ",
                    ),
                );

                if trig.iter().fold(false, |acc, t| acc || !t.0.is_empty()) {
                    res = res
                        .append(" [")
                        .append(alloc.intersperse(trig.iter().map(|t| t.pretty(alloc)), " | "))
                        .append("]");
                }

                res.append(" . ").append(exp.pretty(alloc))
            }
            Exp::Exists(binders, trig, exp) => {
                let mut res = alloc.text("exists ").append(
                    alloc.intersperse(
                        binders
                            .iter()
                            .map(|(b, t)| b.pretty(alloc).append(" : ").append(t.pretty(alloc))),
                        ", ",
                    ),
                );

                if trig.iter().fold(false, |acc, t| acc || !t.0.is_empty()) {
                    res = res
                        .append(" [")
                        .append(alloc.intersperse(trig.iter().map(|t| t.pretty(alloc)), " | "))
                        .append("]");
                }

                res.append(" . ").append(exp.pretty(alloc))
            }
            Exp::Impl(hyp, exp) => {
                let hyp = parens!(alloc, self, hyp);
                let impl_ = alloc
                    .line()
                    .append(alloc.text(" -> "))
                    .append(parens!(alloc, self, exp))
                    .group();

                hyp.append(impl_)
            }
            Exp::Ascribe(e, t) => {
                parens!(alloc, self, e).append(" : ").append(t.pretty(alloc)).group()
            }
            Exp::Old(e) => alloc.text("old").append(e.pretty(alloc).parens()),
            Exp::RecUp { record, updates } => alloc
                .space()
                .append(parens!(alloc, self.precedence().next(), record))
                .append(" with ")
                .append(
                    alloc
                        .intersperse(
                            updates.iter().map(|(nm, a)| {
                                alloc.text(nm).append(" = ").append(parens!(
                                    alloc,
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
                                alloc.text(nm).append(" = ").append(parens!(
                                    alloc,
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Binder::Wild => alloc.text("_"),
            Binder::UnNamed(ty) => ty.pretty(alloc),
            Binder::Named(id) => id.pretty(alloc),
            Binder::Typed(ghost, ids, ty) => {
                (if *ghost { alloc.text("ghost ") } else { alloc.nil() })
                    .append(
                        alloc
                            .intersperse(ids.iter().map(|id| id.pretty(alloc)), alloc.space())
                            .append(" : ")
                            .append(ty.pretty(alloc)),
                    )
                    .parens()
            }
        }
    }
}

impl Print for Pattern {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Pattern::Wildcard => alloc.text("_"),
            Pattern::VarP(v) => v.pretty(alloc),
            Pattern::TupleP(pats) => {
                alloc.intersperse(pats.iter().map(|p| p.pretty(alloc)), ", ").parens()
            }
            Pattern::ConsP(c, pats) => {
                let mut doc = c.pretty(alloc);

                if !pats.is_empty() {
                    doc = doc.append(alloc.space()).append(alloc.intersperse(
                        pats.iter().map(|p| {
                            if matches!(p, Pattern::ConsP(_, _)) {
                                p.pretty(alloc).parens()
                            } else {
                                p.pretty(alloc)
                            }
                        }),
                        " ",
                    ))
                }
                doc
            }
            Pattern::RecP(pats) => {
                let pats = pats.iter().map(|(field, pat)| {
                    field.pretty(alloc).append(" = ").append(pat.pretty(alloc))
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
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
                alloc.as_string(c).append(" : ").append(t.pretty(alloc)).parens()
            }
            Constant::Int(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc)).parens()
            }
            Constant::Int(i, None) => alloc.as_string(i),
            Constant::Uint(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc)).parens()
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
                alloc.text(f_str).append(" : ").append(t.pretty(alloc)).parens()
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let ty_decl = match self {
            TyDecl::Opaque { ty_name, ty_params } => {
                let mut decl = alloc.text("type ").append(ty_name.pretty(alloc));

                if !ty_params.is_empty() {
                    decl = decl.append(" ").append(alloc.intersperse(
                        ty_params.iter().map(|p| alloc.text("'").append(p.pretty(alloc))),
                        alloc.space(),
                    ));
                }
                decl
            }
            TyDecl::Alias { ty_name, ty_params, alias } => alloc
                .text("type ")
                .append(ty_name.pretty(alloc))
                .append(" ")
                .append(alloc.intersperse(
                    ty_params.iter().map(|p| alloc.text("'").append(p.pretty(alloc))),
                    alloc.space(),
                ))
                .append(alloc.text(" =").append(alloc.hardline()))
                .append(alias.pretty(alloc).indent(2)),
            TyDecl::Adt { tys } => {
                let header = once("type").chain(repeat("with"));

                let mut decls = Vec::new();

                for (hdr, AdtDecl { ty_name, ty_params, sumrecord }) in header.zip(tys.iter()) {
                    let decl = alloc
                        .nil()
                        .append(hdr)
                        .append(" ")
                        .append(ty_name.pretty(alloc))
                        .append(" ")
                        .append(alloc.intersperse(
                            ty_params.iter().map(|p| alloc.text("'").append(p.pretty(alloc))),
                            alloc.space(),
                        ));
                    let inner_doc = match sumrecord {
                        SumRecord::Sum(constrs) => alloc.intersperse(
                            constrs.iter().map(|cons| alloc.text("| ").append(cons.pretty(alloc))),
                            alloc.hardline(),
                        ),
                        SumRecord::Record(fields) => alloc
                            .nil()
                            .append(alloc.space())
                            .append(
                                alloc
                                    .intersperse(
                                        fields.iter().map(|f| f.pretty(alloc)),
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

                alloc.intersperse(decls, alloc.hardline())
            }
        };

        ty_decl
    }
}

impl Print for ConstructorDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut cons_doc = self.name.pretty(alloc);

        if !self.fields.is_empty() {
            cons_doc = cons_doc.append(alloc.space()).append(
                alloc.intersperse(self.fields.iter().map(|ty_arg| ty_parens!(alloc, ty_arg)), " "),
            );
        }

        cons_doc
    }
}

impl Print for FieldDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(&self.name).append(alloc.text(": ")).append(self.ty.pretty(alloc))
    }
}

impl Print for Ident {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(&self.0)
    }
}

impl Print for QName {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let module_path = self.module.iter().map(|t| alloc.text(&t.0));
        alloc.intersperse(module_path.chain([alloc.text(self.name.0.clone())]), ".")
    }
}
