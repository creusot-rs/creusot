use std::{fmt::Display, iter::once};

use super::*;
use crate::{
    declaration::*,
    exp::{AssocDir, BinOp, Constant, Precedence, UnOp},
};
use pretty::*;

#[derive(Default)]
pub struct PrintEnv {
    pub scopes: Vec<Ident>,
}

impl PrintEnv {
    pub fn new() -> (BoxAllocator, Self) {
        (BoxAllocator, PrintEnv::default())
    }
}

pub struct PrintDisplay<'a, A: Print>(&'a A);

impl<'a, A: Print> Display for PrintDisplay<'a, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (alloc, mut env) = PrintEnv::new();
        self.0.pretty(&alloc, &mut env).1.render_fmt(120, f)?;
        Ok(())
    }
}

pub trait Print {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
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

use itertools::*;

// TODO: replace with functions
macro_rules! parens {
    ($alloc:ident, $env:ident, $parent:ident, $child:ident) => {
        parens($alloc, $env, $parent.precedence(), $child)
    };
    ($alloc:ident, $env:ident, $par_prec:expr, $child:ident) => {
        parens($alloc, $env, $par_prec, $child)
    };
}

fn parens<'b, 'a: 'b, A: DocAllocator<'a>>(
    alloc: &'a A,
    env: &mut PrintEnv,
    prec: Precedence,
    child: &'a Exp,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    let child_prec = child.precedence();
    if child_prec == Precedence::Atom {
        child.pretty(alloc, env)
    } else if child_prec < prec {
        child.pretty(alloc, env).parens()
    } else if child_prec == prec && child.associativity() != child.associativity() {
        child.pretty(alloc, env).parens()
    } else {
        child.pretty(alloc, env)
    }
}

impl Print for Decl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Decl::FunDecl(fun) => fun.pretty(alloc, env),
            Decl::LogicDecl(log) => log.pretty(alloc, env),
            Decl::Module(modl) => modl.pretty(alloc, env),
            Decl::Scope(scope) => scope.pretty(alloc, env),
            Decl::PredDecl(p) => p.pretty(alloc, env),
            Decl::TyDecl(t) => t.pretty(alloc, env),
            Decl::Clone(c) => c.pretty(alloc, env),
            Decl::ValDecl(v) => v.pretty(alloc, env),
            Decl::UseDecl(u) => u.pretty(alloc, env),
            Decl::Axiom(a) => a.pretty(alloc, env),
            Decl::Goal(g) => g.pretty(alloc, env),
            Decl::Let(l) => l.pretty(alloc, env),
            Decl::LetFun(l) => l.pretty(alloc, env),
        }
    }
}

impl Print for Module {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        env.scopes.push(self.name.clone());
        let doc = alloc
            .text("module ")
            .append(&*self.name)
            .append(alloc.hardline())
            .append(
                alloc
                    .intersperse(
                        self.decls.iter().map(|decl| decl.pretty(alloc, env)),
                        alloc.hardline(),
                    )
                    .indent(2),
            )
            .append(alloc.hardline())
            .append("end");
        env.scopes.pop();
        doc
    }
}

impl Print for Scope {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        env.scopes.push(self.name.clone());
        let doc = alloc
            .text("scope")
            .append(alloc.space())
            .append(&self.name.0)
            .append(alloc.hardline())
            .append(
                alloc
                    .intersperse(
                        self.decls.iter().map(|decl| decl.pretty(alloc, env)),
                        alloc.hardline(),
                    )
                    .indent(2),
            )
            .append(alloc.hardline())
            .append("end");
        env.scopes.pop();
        doc
    }
}

impl Print for Axiom {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("axiom ")
            .append(self.name.pretty(alloc, env))
            .append(" : ")
            .append(self.axiom.pretty(alloc, env))
    }
}

impl Print for Goal {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("goal ")
            .append(self.name.pretty(alloc, env))
            .append(" : ")
            .append(self.goal.pretty(alloc, env))
    }
}

impl Print for LetDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut doc = alloc.text("let ");

        if self.rec {
            doc = doc.append("rec ");
        }

        if self.constant {
            doc = doc.append("constant ");
        }

        doc = doc
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, env).indent(2));

        doc
    }
}

impl Print for LetFun {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
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

        doc = doc
            .append("function ")
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, env).indent(2));

        doc
    }
}

impl Print for Attribute {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        self.name
            .pretty(alloc, env)
            .append(alloc.space())
            .append(alloc.intersperse(
                self.attrs.iter().map(|a| a.pretty(alloc, env)).chain(once(alloc.nil())),
                alloc.space(),
            ))
            .append(arg_list(alloc, env, &self.args))
            .append(
                self.retty.as_ref().map_or_else(
                    || alloc.nil(),
                    |t| alloc.text(" : ").append(t.pretty(alloc, env)),
                ),
            )
            .append(alloc.line_().append(self.contract.pretty(alloc, env)))
            .nest(2)
            .group()
        // .append(alloc.line())
        // .append(self.contract.pretty(alloc, env).indent(2))
    }
}

impl Print for Predicate {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("predicate ")
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, env).indent(2))
    }
}

fn arg_list<'b: 'a, 'a, A: DocAllocator<'a>>(
    alloc: &'a A,
    env: &mut PrintEnv,
    args: &'a [(Ident, Type)],
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    {
        alloc.intersperse(
            args.iter().map(|(id, ty)| {
                id.pretty(alloc, env).append(" : ").append(ty.pretty(alloc, env)).parens()
            }),
            alloc.space(),
        )
    }
}

impl Print for Logic {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("function ")
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, env).indent(2))
    }
}

impl Print for DeclClone {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
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

        let doc =
            alloc.text("clone ").append(kind).append(self.name.pretty(alloc, env)).append(as_doc);

        if self.subst.is_empty() {
            doc
        } else {
            doc.append(" with ").append(alloc.intersperse(
                self.subst.iter().map(|s| s.pretty(alloc, env)),
                alloc.text(",").append(alloc.softline()),
            ))
        }
    }
}

impl Print for CloneSubst {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            CloneSubst::Type(id, ty) => alloc
                .text("type ")
                .append(id.pretty(alloc, env))
                .append(" = ")
                .append(ty.pretty(alloc, env)),
            CloneSubst::Val(id, o) => alloc
                .text("val ")
                .append(id.pretty(alloc, env))
                .append(" = ")
                .append(o.pretty(alloc, env)),
            CloneSubst::Predicate(id, o) => alloc
                .text("predicate ")
                .append(id.pretty(alloc, env))
                .append(" = ")
                .append(o.pretty(alloc, env)),
            CloneSubst::Function(id, o) => alloc
                .text("function ")
                .append(id.pretty(alloc, env))
                .append(" = ")
                .append(o.pretty(alloc, env)),
            CloneSubst::Axiom(id) => match id {
                Some(id) => alloc.text("axiom ").append(id.pretty(alloc, env)),
                None => alloc.text("axiom ."),
            },
        }
    }
}

impl Print for Use {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text("use ").append(self.name.pretty(alloc, env))
    }
}

impl Print for ValKind {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            ValKind::Val { sig } => alloc.text("val ").append(sig.pretty(alloc, env)),
            ValKind::Predicate { sig } => alloc.text("predicate ").append(sig.pretty(alloc, env)),
            ValKind::Function { sig } => alloc.text("function ").append(sig.pretty(alloc, env)),
        }
    }
}

impl Print for Contract {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut doc = alloc.nil();

        for req in &self.requires {
            doc = doc.append(
                alloc
                    .text("requires ")
                    .append(req.pretty(alloc, env).braces())
                    .append(alloc.hardline()),
            )
        }

        for req in &self.ensures {
            doc = doc.append(
                alloc
                    .text("ensures ")
                    .append(
                        alloc.space().append(req.pretty(alloc, env)).append(alloc.space()).braces(),
                    )
                    .append(alloc.hardline()),
            )
        }

        for var in &self.variant {
            doc = doc.append(
                alloc
                    .text("variant ")
                    .append(var.pretty(alloc, env).braces())
                    .append(alloc.hardline()),
            )
        }

        doc
    }
}

impl Print for CfgFunction {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("let ")
            .append(if self.rec { "rec " } else { "" })
            .append("cfg ")
            .append(if self.constant { "constant " } else { "" })
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" =")))
            .group()
            .append(alloc.line())
            .append(sep_end_by(
                alloc,
                self.vars.iter().map(|(ghost, var, ty)| {
                    if *ghost { alloc.text("ghost var ") } else { alloc.text("var ") }
                        .append(alloc.as_string(&var.0))
                        .append(" : ")
                        .append(ty.pretty(alloc, env))
                        .append(";")
                }),
                alloc.hardline(),
            ))
            .append(self.entry.pretty(alloc, env).append(alloc.hardline()))
            .append(sep_end_by(
                alloc,
                self.blocks.iter().map(|(id, block)| {
                    id.pretty(alloc, env).append(alloc.space()).append(block.pretty(alloc, env))
                }),
                alloc.hardline(),
            ))
    }
}

impl Print for Type {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use Type::*;

        macro_rules! ty_parens {
            ($alloc:ident, $env:ident, $e:ident) => {
                if $e.complex() {
                    $e.pretty($alloc, $env).parens()
                } else {
                    $e.pretty($alloc, $env)
                }
            };
        }
        match self {
            Bool => alloc.text("bool"),
            Char => alloc.text("char"),
            Integer => alloc.text("int"),
            MutableBorrow(box t) => alloc.text("borrowed ").append(ty_parens!(alloc, env, t)),
            TVar(v) => alloc.text(format!("'{}", v.0)),
            TConstructor(ty) => ty.pretty(alloc, env),

            TFun(box a, box b) => {
                ty_parens!(alloc, env, a).append(" -> ").append(ty_parens!(alloc, env, b))
            }
            TApp(box tyf, args) => {
                if args.is_empty() {
                    tyf.pretty(alloc, env)
                } else {
                    tyf.pretty(alloc, env).append(alloc.space()).append(alloc.intersperse(
                        args.iter().map(|arg| ty_parens!(alloc, env, arg)),
                        alloc.space(),
                    ))
                }
            }
            Tuple(tys) => alloc
                .intersperse(tys.iter().map(|ty| ty.pretty(alloc, env)), alloc.text(", "))
                .parens(),
        }
    }
}

impl Print for Exp {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Exp::Any(ty) => alloc.text("any ").append(ty.pretty(alloc, env)),
            Exp::Current(box e) => alloc.text(" * ").append(parens!(alloc, env, self, e)),
            Exp::Final(box e) => alloc.text(" ^ ").append(parens!(alloc, env, self, e)),
            // TODO parenthesization
            Exp::Let { pattern, box arg, box body } => alloc
                .text("let ")
                .append(pattern.pretty(alloc, env))
                .append(" = ")
                .append(parens!(alloc, env, self, arg))
                .append(" in ")
                .append(body.pretty(alloc, env)),
            Exp::Var(v, _) => v.pretty(alloc, env),
            Exp::QVar(v, _) => v.pretty(alloc, env),
            Exp::RecUp { box record, label, box val } => alloc
                .space()
                .append(parens!(alloc, env, self.precedence().next(), record))
                .append(" with ")
                .append(alloc.text(label))
                .append(" = ")
                .append(parens!(alloc, env, self, val))
                .append(alloc.space())
                .braces(),
            Exp::RecField { box record, label } => {
                record.pretty(alloc, env).append(".").append(label)
            }

            Exp::Tuple(args) => {
                alloc.intersperse(args.iter().map(|a| a.pretty(alloc, env)), ", ").parens()
            }

            Exp::Constructor { ctor, args } => ctor.pretty(alloc, env).append(if args.is_empty() {
                alloc.nil()
            } else {
                alloc.space().append(alloc.intersperse(
                    args.iter().map(|a| parens!(alloc, env, Precedence::Brackets, a)),
                    " ",
                ))
            }),

            Exp::BorrowMut(box exp) => {
                alloc.text("borrow_mut ").append(parens!(alloc, env, self.precedence().next(), exp))
            }

            Exp::Const(c) => c.pretty(alloc, env),

            Exp::UnaryOp(UnOp::Not, box op) => {
                alloc.text("not ").append(parens!(alloc, env, self, op))
            }

            Exp::UnaryOp(UnOp::Neg, box op) => alloc.text("- ").append(op.pretty(alloc, env)),
            Exp::BinaryOp(op, box l, box r) => match self.associativity() {
                Some(AssocDir::Left) => parens!(alloc, env, self, l),
                Some(AssocDir::Right) | None => parens!(alloc, env, self.precedence().next(), l),
            }
            .append(alloc.space())
            .append(bin_op_to_string(op))
            .append(alloc.space())
            .append(match self.associativity() {
                Some(AssocDir::Right) => parens!(alloc, env, self, r),
                Some(AssocDir::Left) | None => parens!(alloc, env, self.precedence().next(), r),
            }),
            Exp::Call(box fun, args) => {
                parens!(alloc, env, self, fun).append(alloc.space()).append(alloc.intersperse(
                    args.iter().map(|a| parens!(alloc, env, Precedence::App.next(), a)),
                    alloc.space(),
                ))
            }

            Exp::Verbatim(verb) => alloc.text(verb),
            Exp::Attr(attr, e) => {
                attr.pretty(alloc, env).append(alloc.space()).append(e.pretty(alloc, env))
            }
            Exp::Abs(ident, box body) => alloc
                .text("fun ")
                .append(ident.pretty(alloc, env))
                .append(" -> ")
                .append(body.pretty(alloc, env)),

            Exp::Match(box scrut, brs) => alloc
                .text("match ")
                .append(scrut.pretty(alloc, env).parens())
                .append(" with")
                .append(alloc.hardline())
                .append(
                    sep_end_by(
                        alloc,
                        brs.iter().map(|(pat, br)| {
                            alloc
                                .text("| ")
                                .append(pat.pretty(alloc, env))
                                .append(" -> ")
                                .append(br.pretty(alloc, env))
                        }),
                        alloc.hardline(),
                    )
                    .indent(2),
                )
                .append("end"),
            Exp::IfThenElse(s, i, e) => alloc
                .text("if ")
                .append(s.pretty(alloc, env))
                .append(" then")
                .append(alloc.line().append(i.pretty(alloc, env)).nest(2).append(alloc.line()))
                .append("else")
                .append(alloc.line().append(e.pretty(alloc, env)).nest(2).append(alloc.line_()))
                .group(),
            Exp::Forall(binders, box exp) => alloc
                .text("forall ")
                .append(alloc.intersperse(
                    binders.iter().map(|(b, t)| {
                        b.pretty(alloc, env).append(" : ").append(t.pretty(alloc, env))
                    }),
                    alloc.text(", "),
                ))
                .append(" . ")
                .append(exp.pretty(alloc, env)),
            Exp::Exists(binders, box exp) => alloc
                .text("exists ")
                .append(alloc.intersperse(
                    binders.iter().map(|(b, t)| {
                        b.pretty(alloc, env).append(" : ").append(t.pretty(alloc, env))
                    }),
                    alloc.text(", "),
                ))
                .append(" . ")
                .append(exp.pretty(alloc, env)),
            Exp::Impl(box hyp, box exp) => {
                parens!(alloc, env, self, hyp).append(" -> ").append(parens!(alloc, env, self, exp))
            }
            Exp::Ascribe(e, t) => {
                e.pretty(alloc, env).append(" : ").append(t.pretty(alloc, env)).group()
            }
            Exp::Pure(e) => alloc.text("pure ").append(e.pretty(alloc, env).braces()),
            Exp::Ghost(e) => {
                alloc.text("ghost ").append(parens!(alloc, env, Precedence::App.next(), e))
            }
            Exp::Absurd => alloc.text("absurd"),
            Exp::Old(e) => alloc.text("old").append(e.pretty(alloc, env).parens()),
        }
    }
}

impl Print for Statement {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Statement::Assign { lhs, rhs } => lhs
                .pretty(alloc, env)
                .append(" <- ")
                .append(parens!(alloc, env, Precedence::Impl, rhs)),
            Statement::Invariant(nm, e) => {
                let doc =
                    alloc.text("invariant ").append(alloc.text(nm)).append(alloc.space()).append(
                        alloc.space().append(e.pretty(alloc, env)).append(alloc.space()).braces(),
                    );
                doc
            }
            Statement::Assume(assump) => {
                let doc = alloc.text("assume ").append(
                    alloc.space().append(assump.pretty(alloc, env)).append(alloc.space()).braces(),
                );
                doc
            }
            Statement::Assert(assert) => {
                let doc = alloc.text("assert ").append(
                    alloc.space().append(assert.pretty(alloc, env)).append(alloc.space()).braces(),
                );
                doc
            }
        }
    }
}

impl Print for Terminator {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use Terminator::*;
        match self {
            Goto(tgt) => alloc.text("goto ").append(tgt.pretty(alloc, env)),
            Absurd => alloc.text("absurd"),
            Return => alloc.text("return _0"),
            Switch(discr, brs) => alloc
                .text("switch ")
                .append(discr.pretty(alloc, env).parens())
                .append(alloc.hardline())
                .append(
                    sep_end_by(
                        alloc,
                        brs.iter().map(|(pat, tgt)| {
                            alloc
                                .text("| ")
                                .append(pat.pretty(alloc, env))
                                .append(" -> ")
                                .append(tgt.pretty(alloc, env))
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Pattern::Wildcard => alloc.text("_"),
            Pattern::VarP(v) => v.pretty(alloc, env),
            Pattern::TupleP(pats) => alloc
                .intersperse(pats.iter().map(|p| p.pretty(alloc, env)), alloc.text(", "))
                .parens(),
            Pattern::ConsP(c, pats) => {
                let mut doc = c.pretty(alloc, env);

                if !pats.is_empty() {
                    doc = doc.append(alloc.space()).append(alloc.intersperse(
                        pats.iter().map(|p| {
                            if matches!(p, Pattern::ConsP(_, _)) {
                                p.pretty(alloc, env).parens()
                            } else {
                                p.pretty(alloc, env)
                            }
                        }),
                        alloc.text(" "),
                    ))
                }
                doc
            }
        }
    }
}

impl Print for BlockId {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
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
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .hardline()
            .append(
                sep_end_by(
                    alloc,
                    self.statements.iter().map(|stmt| stmt.pretty(alloc, env)),
                    alloc.text(";").append(alloc.line()),
                )
                .append(self.terminator.pretty(alloc, env)),
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
    }
}

impl Print for Constant {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
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
            Constant::Int(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc, env)).parens()
            }
            Constant::Int(i, None) => alloc.as_string(i),
            Constant::Uint(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc, env)).parens()
            }
            Constant::String(s) => alloc.text(s).double_quotes(),
            Constant::Uint(i, None) => alloc.as_string(i),
        }
    }
}

impl Print for TyDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let ty_decl = match self {
            TyDecl::Opaque { ty_name, ty_params } => {
                let mut decl = alloc.text("type ").append(ty_name.pretty(alloc, env));

                if !ty_params.is_empty() {
                    decl = decl.append(" ").append(alloc.intersperse(
                        ty_params.iter().map(|p| alloc.text("'").append(p.pretty(alloc, env))),
                        alloc.space(),
                    ));
                }
                decl
            }
            TyDecl::Alias { ty_name, ty_params, alias } => alloc
                .text("type ")
                .append(ty_name.pretty(alloc, env))
                .append(" ")
                .append(alloc.intersperse(
                    ty_params.iter().map(|p| alloc.text("'").append(p.pretty(alloc, env))),
                    alloc.space(),
                ))
                .append(alloc.text(" =").append(alloc.hardline()))
                .append(alias.pretty(alloc, env).indent(2)),
            TyDecl::Adt { tys } => {
                use std::iter::*;
                let header = once("type").chain(repeat("with"));
                let mut decl = alloc.nil();

                for (hdr, ty_decl) in header.zip(tys.iter()) {
                    decl =
                        decl.append(hdr)
                            .append(" ")
                            .append(ty_decl.ty_name.pretty(alloc, env))
                            .append(" ")
                            .append(alloc.intersperse(
                                ty_decl
                                    .ty_params
                                    .iter()
                                    .map(|p| alloc.text("'").append(p.pretty(alloc, env))),
                                alloc.space(),
                            ));

                    let mut inner_doc = alloc.nil();
                    for cons in &ty_decl.constrs {
                        let ty_cons = alloc.text("| ").append(cons.pretty(alloc, env));
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
        //     alloc.text("type ").append(self.ty_name.pretty(alloc, env)).append(" ").append(
        //         alloc.intersperse(
        //             self.ty_params.iter().map(|p| alloc.text("'").append(p.pretty(alloc, env))),
        //             alloc.space(),
        //         ),
        //     );

        // if !matches!(self, TyDecl::Opaque { .. }) {
        //     ty_decl = ty_decl.append(alloc.text(" =").append(alloc.hardline()));
        // }
        ty_decl
        // ty_decl.append(self.kind.pretty(alloc, env).indent(2))
    }
}

impl Print for ConstructorDecl {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut cons_doc = self.name.pretty(alloc, env);

        if !self.fields.is_empty() {
            cons_doc = cons_doc.append(alloc.space()).append(alloc.intersperse(
                self.fields.iter().map(|ty_arg| {
                    if !ty_arg.complex() {
                        ty_arg.pretty(alloc, env)
                    } else {
                        ty_arg.pretty(alloc, env).parens()
                    }
                }),
                alloc.text(" "),
            ));
        }

        cons_doc
    }
}

// impl Print for TyDeclKind {
//     fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
//         &'a self,
//         alloc: &'a A,
//         env: &mut PrintEnv,
//     ) -> DocBuilder<'a, A>
//     where
//         A::Doc: Clone,
//     {
//         match self {
//             TyDeclKind::Adt(cons) => {
//                 let mut inner_doc = alloc.nil();
//                 for (cons, args) in cons {
//                     let mut ty_cons = alloc.text("| ").append(alloc.text(cons));

//                     if !args.is_empty() {
//                         ty_cons = ty_cons.append(alloc.space()).append(alloc.intersperse(
//                             args.iter().map(|ty_arg| {
//                                 if !ty_arg.complex() {
//                                     ty_arg.pretty(alloc, env)
//                                 } else {
//                                     ty_arg.pretty(alloc, env).parens()
//                                 }
//                             }),
//                             alloc.text(" "),
//                         ))
//                     }

//                     inner_doc = inner_doc.append(ty_cons.append(alloc.hardline()))
//                 }

//                 inner_doc
//             }
//             TyDeclKind::Alias(t) => t.pretty(alloc, env),
//             TyDeclKind::Opaque => alloc.nil(),
//         }
//     }
// }

impl Print for Ident {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text(&self.0)
    }
}

impl Print for QName {
    fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use itertools::EitherOrBoth::*;
        // Strip the shared prefix between currently open scope and the identifier we are printing
        let module_path = env
            .scopes
            .iter()
            .zip_longest(self.module.iter())
            // Skip the common prefix, and keep everything else.
            .skip_while(|e| match e {
                // Skip common prefix
                Both(p, m) => p == m,
                _ => false,
            })
            // If the opened scopes were longer, drop them
            .filter(|e| !e.is_left())
            .map(|t| t.reduce(|_, f| f))
            // TODO investigate if this clone can be removed :/
            .map(|t| alloc.text(t.0.clone()));

        alloc.intersperse(
            module_path.chain(std::iter::once(alloc.text(self.name().0))),
            alloc.text("."),
        )
    }
}
