use std::{fmt::Display, iter::once};

use super::*;
use crate::{
    declaration::{self, *},
    exp::{AssocDir, BinOp, Binder, Constant, Precedence, Trigger, UnOp},
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

impl Print for Decl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Decl::CfgDecl(fun) => fun.pretty(alloc),
            Decl::LogicDefn(log) => log.pretty(alloc),
            Decl::Module(modl) => modl.pretty(alloc),
            Decl::Scope(scope) => scope.pretty(alloc),
            Decl::PredDecl(p) => p.pretty(alloc),
            Decl::TyDecl(t) => t.pretty(alloc),
            Decl::Clone(c) => c.pretty(alloc),
            Decl::ValDecl(v) => v.pretty(alloc),
            Decl::UseDecl(u) => u.pretty(alloc),
            Decl::Axiom(a) => a.pretty(alloc),
            Decl::Goal(g) => g.pretty(alloc),
            Decl::Let(l) => l.pretty(alloc),
            Decl::ConstantDecl(c) => c.pretty(alloc),
            Decl::Coma(d) => d.pretty(alloc),
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
            .append(alloc.hardline())
            .append(
                alloc
                    .intersperse(self.decls.iter().map(|decl| decl.pretty(alloc)), alloc.hardline())
                    .indent(2),
            )
            .append(alloc.hardline())
            .append("end");
        doc
    }
}

impl Print for Scope {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let doc = alloc
            .text("scope")
            .append(alloc.space())
            .append(&self.name.0)
            .append(alloc.hardline())
            .append(
                alloc
                    .intersperse(self.decls.iter().map(|decl| decl.pretty(alloc)), alloc.hardline())
                    .indent(2),
            )
            .append(alloc.hardline())
            .append("end");
        doc
    }
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
        alloc
            .text("constant ")
            .append(self.name.pretty(alloc))
            .append(" : ")
            .append(self.type_.pretty(alloc))
            .append(" = ")
            .append(self.body.pretty(alloc))
    }
}

impl Print for LetDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut doc = alloc.text("let ");

        if self.rec {
            doc = doc.append("rec ");
        }

        if self.ghost {
            doc = doc.append("ghost ");
        }

        match self.kind {
            Some(LetKind::Function) => doc = doc.append("function "),
            Some(LetKind::Predicate) => doc = doc.append("predicate "),
            Some(LetKind::Constant) => doc = doc.append("constant "),
            None => {}
        }

        doc = doc
            .append(
                self.sig
                    .pretty(alloc)
                    .append(alloc.line_())
                    .append(alloc.text(" = [@vc:do_not_keep_trace] [@vc:sp]")),
            )
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc).indent(2));

        doc
    }
}

impl Print for Attribute {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match &self {
            Attribute::Attr(s) => alloc.text("@").append(s),
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
    {
        alloc.intersperse(args.iter().map(|b| b.pretty(alloc)), alloc.space())
    }
}

impl Print for Logic {
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

impl Print for DeclClone {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let as_doc = match &self.kind {
            CloneKind::Named(nm) => alloc.text(" as ").append(&**nm),
            _ => alloc.nil(),
        };
        let kind = match &self.kind {
            CloneKind::Export => alloc.text("export "),
            _ => alloc.nil(),
        };

        let doc = alloc.text("clone ").append(kind).append(self.name.pretty(alloc)).append(as_doc);

        if self.subst.is_empty() {
            doc
        } else {
            doc.append(" with").append(alloc.hardline()).append(
                alloc
                    .intersperse(
                        self.subst.iter().map(|s| s.pretty(alloc)),
                        alloc.text(",").append(alloc.hardline()),
                    )
                    .indent(2),
            )
        }
    }
}

impl Print for CloneSubst {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            CloneSubst::Type(id, ty) => {
                alloc.text("type ").append(id.pretty(alloc)).append(" = ").append(ty.pretty(alloc))
            }
            CloneSubst::Val(id, o) => {
                alloc.text("val ").append(id.pretty(alloc)).append(" = ").append(o.pretty(alloc))
            }
            CloneSubst::Predicate(id, o) => alloc
                .text("predicate ")
                .append(id.pretty(alloc))
                .append(" = ")
                .append(o.pretty(alloc)),
            CloneSubst::Function(id, o) => alloc
                .text("function ")
                .append(id.pretty(alloc))
                .append(" = ")
                .append(o.pretty(alloc)),
            CloneSubst::Axiom(id) => match id {
                Some(id) => alloc.text("axiom ").append(id.pretty(alloc)),
                None => alloc.text("axiom ."),
            },
        }
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
            .append(self.name.pretty(alloc))
            .append(if let Some(as_) = &self.as_ {
                alloc.text(" as ").append(as_.pretty(alloc))
            } else {
                alloc.nil()
            })
    }
}

impl Print for ValDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut doc = alloc.nil();

        if self.val {
            doc = doc.append("val ");
        }

        if self.ghost {
            doc = doc.append("ghost ");
        }

        match self.kind {
            Some(LetKind::Function) => doc = doc.append("function "),
            Some(LetKind::Predicate) => doc = doc.append("predicate "),
            Some(LetKind::Constant) => doc = doc.append("constant "),
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
                alloc.text("requires ").append(req.pretty(alloc).braces()).append(alloc.hardline()),
            )
        }

        for req in &self.ensures {
            doc = doc.append(
                alloc
                    .text("ensures ")
                    .append(alloc.space().append(req.pretty(alloc)).append(alloc.space()).braces())
                    .append(alloc.hardline()),
            )
        }

        for var in &self.variant {
            doc = doc.append(
                alloc.text("variant ").append(var.pretty(alloc).braces()).append(alloc.hardline()),
            )
        }

        doc
    }
}

impl Print for CfgFunction {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("let ")
            .append(if self.rec { "rec " } else { "" })
            .append("cfg ")
            .append(if self.constant { "constant " } else { "" })
            .append(
                self.sig
                    .pretty(alloc)
                    .append(alloc.line_())
                    .append(alloc.text(" = [@vc:do_not_keep_trace] [@vc:sp]")),
            )
            .group()
            .append(alloc.line())
            .append(sep_end_by(
                alloc,
                self.vars.iter().map(|(ghost, var, ty, init)| {
                    if *ghost { alloc.text("ghost var ") } else { alloc.text("var ") }
                        .append(alloc.as_string(&var.0))
                        .append(" : ")
                        .append(ty.pretty(alloc))
                        .append(if let Some(init) = init {
                            alloc.text(" = ").append(init.pretty(alloc))
                        } else {
                            alloc.nil()
                        })
                        .append(";")
                }),
                alloc.hardline(),
            ))
            .append(self.entry.pretty(alloc).append(alloc.hardline()))
            .append(sep_end_by(
                alloc,
                self.blocks.iter().map(|(id, block)| {
                    id.pretty(alloc).append(alloc.space()).append(block.pretty(alloc))
                }),
                alloc.hardline(),
            ))
    }
}

impl Print for Type {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use Type::*;

        macro_rules! ty_parens {
            ($alloc:ident, $e:ident) => {
                if $e.complex() {
                    $e.pretty($alloc).parens()
                } else {
                    $e.pretty($alloc)
                }
            };
        }
        match self {
            Bool => alloc.text("bool"),
            Char => alloc.text("char"),
            Integer => alloc.text("int"),
            MutableBorrow(t) => alloc.text("borrowed ").append(ty_parens!(alloc, t)),
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
        match &self.0 {
            None => alloc.nil(),
            Some(exp) => exp.pretty(alloc).brackets(),
        }
    }
}

impl Print for Exp {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Exp::Any(ty) => alloc.text("any ").append(ty.pretty(alloc)),
            Exp::Current(e) => alloc.text(" * ").append(parens!(alloc, self, e)),
            Exp::Final(e) => alloc.text(" ^ ").append(parens!(alloc, self, e)),
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
            Exp::RecUp { record, updates } => {
                let mut res = alloc
                    .space()
                    .append(parens!(alloc, self.precedence().next(), record))
                    .append(" with ");
                for (label, val) in updates {
                    res = res
                        .append(alloc.text(label))
                        .append(" = ")
                        .append(parens!(alloc, self, val))
                        .append(" ; ");
                }
                res.braces()
            }
            Exp::RecField { record, label } => record.pretty(alloc).append(".").append(label),

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

            Exp::Verbatim(verb) => alloc.text(verb),
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
                    .indent(2),
                )
                .append("end"),
            Exp::IfThenElse(s, i, e) => alloc
                .text("if ")
                .append(s.pretty(alloc))
                .append(" then")
                .append(alloc.line().append(i.pretty(alloc)).nest(2).append(alloc.line()))
                .append("else")
                .append(alloc.line().append(e.pretty(alloc)).nest(2).append(alloc.line_()))
                .group(),
            Exp::Forall(binders, trig, exp) => alloc
                .text("forall ")
                .append(
                    alloc.intersperse(
                        binders
                            .iter()
                            .map(|(b, t)| b.pretty(alloc).append(" : ").append(t.pretty(alloc))),
                        ", ",
                    ),
                )
                .append(trig.pretty(alloc))
                .append(" . ")
                .append(exp.pretty(alloc)),
            Exp::Exists(binders, trig, exp) => alloc
                .text("exists ")
                .append(
                    alloc.intersperse(
                        binders
                            .iter()
                            .map(|(b, t)| b.pretty(alloc).append(" : ").append(t.pretty(alloc))),
                        ", ",
                    ),
                )
                .append(trig.pretty(alloc))
                .append(" . ")
                .append(exp.pretty(alloc)),
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
            Exp::Pure(e) => alloc.text("pure ").append(e.pretty(alloc).braces()),
            Exp::Ghost(e) => alloc.text("ghost ").append(parens!(alloc, Precedence::App.next(), e)),
            Exp::Absurd => alloc.text("absurd"),
            Exp::Old(e) => alloc.text("old").append(e.pretty(alloc).parens()),
            Exp::Record { fields } => alloc
                .intersperse(
                    fields.iter().map(|(nm, a)| {
                        alloc.text(nm).append(" = ").append(parens!(
                            alloc,
                            Precedence::Attr.next(),
                            a
                        ))
                    }),
                    "; ",
                )
                .braces(),
            Exp::Chain(fields) => alloc.intersperse(fields.iter().map(|f| f.pretty(alloc)), "; "),
            Exp::FnLit(e) => alloc.text("fun _ -> ").append(e.pretty(alloc)).parens(),
            Exp::Assert(e) => alloc.text("assert ").append(e.pretty(alloc).braces()),
            Exp::Assume(e) => alloc.text("assume ").append(e.pretty(alloc).braces()),
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

fn pretty_attr<'b, 'a: 'b, A: DocAllocator<'a>>(
    attr: &'a Option<Attribute>,
    alloc: &'a A,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    match attr {
        Some(attr) => attr.pretty(alloc).append(" "),
        None => alloc.nil(),
    }
}

impl Print for Statement {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Statement::Assign { attr, lhs, rhs } => pretty_attr(attr, alloc)
                .append(lhs.pretty(alloc))
                .append(" <- ")
                .append(parens!(alloc, Precedence::Impl, rhs)),
            Statement::Invariant(e) => {
                let doc = alloc
                    .text("invariant ")
                    .append(alloc.space().append(e.pretty(alloc)).append(alloc.space()).braces());
                doc
            }
            Statement::Variant(e) => {
                let doc = alloc
                    .text("variant ")
                    .append(alloc.space().append(e.pretty(alloc)).append(alloc.space()).braces());
                doc
            }
            Statement::Assume(assump) => {
                let doc = alloc.text("assume ").append(
                    alloc.space().append(assump.pretty(alloc)).append(alloc.space()).braces(),
                );
                doc
            }
            Statement::Assert(assert) => {
                let doc = alloc.text("assert ").append(
                    alloc.space().append(assert.pretty(alloc)).append(alloc.space()).braces(),
                );
                doc
            }
        }
    }
}

impl Print for Terminator {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use Terminator::*;
        match self {
            Goto(tgt) => alloc.text("goto ").append(tgt.pretty(alloc)),
            Absurd => alloc.text("absurd"),
            Return => alloc.text("return _0"),
            Switch(discr, brs) => alloc
                .text("switch ")
                .append(discr.pretty(alloc).parens())
                .append(alloc.hardline())
                .append(
                    sep_end_by(
                        alloc,
                        brs.iter().map(|(pat, tgt)| {
                            alloc
                                .text("| ")
                                .append(pat.pretty(alloc))
                                .append(" -> ")
                                .append(tgt.pretty(alloc))
                        }),
                        alloc.hardline(),
                    )
                    .indent(2),
                )
                .append("end"),
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
        }
    }
}

impl Print for BlockId {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text("BB").append(alloc.as_string(self.0))
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

impl Print for Block {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .hardline()
            .append(
                sep_end_by(
                    alloc,
                    self.statements.iter().map(|stmt| stmt.pretty(alloc)),
                    alloc.text(";").append(alloc.line()),
                )
                .append(self.terminator.pretty(alloc)),
            )
            .nest(2)
            .append(alloc.hardline())
            .braces()
    }
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
                use std::iter::*;
                let header = once("type").chain(repeat("with"));
                let mut decl = alloc.nil();

                for (hdr, ty_decl) in header.zip(tys.iter()) {
                    decl = decl
                        .append(hdr)
                        .append(" ")
                        .append(ty_decl.ty_name.pretty(alloc))
                        .append(" ")
                        .append(
                            alloc.intersperse(
                                ty_decl
                                    .ty_params
                                    .iter()
                                    .map(|p| alloc.text("'").append(p.pretty(alloc))),
                                alloc.space(),
                            ),
                        );

                    let mut inner_doc = alloc.nil();
                    for cons in &ty_decl.constrs {
                        let ty_cons = alloc.text("| ").append(cons.pretty(alloc));
                        inner_doc = inner_doc.append(ty_cons.append(alloc.hardline()))
                    }
                    decl = decl
                        .append(alloc.text(" =").append(alloc.hardline()))
                        .append(inner_doc.indent(2))
                }
                decl
            }
        };

        // let mut ty_decl =
        //     alloc.text("type ").append(self.ty_name.pretty(alloc)).append(" ").append(
        //         alloc.intersperse(
        //             self.ty_params.iter().map(|p| alloc.text("'").append(p.pretty(alloc))),
        //             alloc.space(),
        //         ),
        //     );

        // if !matches!(self, TyDecl::Opaque { .. }) {
        //     ty_decl = ty_decl.append(alloc.text(" =").append(alloc.hardline()));
        // }
        ty_decl
        // ty_decl.append(self.kind.pretty(alloc).indent(2))
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
                alloc.intersperse(self.fields.iter().map(|ty_arg| ty_arg.pretty(alloc)), " "),
            );
        }

        cons_doc
    }
}

impl Print for Field {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(&'a self, alloc: &'a A) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let parens = self.ghost || self.ty.complex();
        let doc = if self.ghost { alloc.text("ghost ") } else { alloc.nil() }
            .append(self.ty.pretty(alloc));

        if parens {
            doc.parens()
        } else {
            doc
        }
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

        alloc.intersperse(module_path.chain(std::iter::once(alloc.text(self.name().0))), ".")
    }
}
