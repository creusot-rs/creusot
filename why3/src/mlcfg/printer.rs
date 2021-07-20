use super::*;
use crate::declaration::*;
use pretty::*;

#[derive(Default)]
pub struct PrintEnv {
    pub scopes: Vec<String>,
    in_logic: bool,
}

impl PrintEnv {
    pub fn new() -> (BoxAllocator, Self) {
        (BoxAllocator, PrintEnv::default())
    }
}

use itertools::*;

// FIXME: Doesn't take into account associativity when deciding when to put parens
macro_rules! parens {
    ($alloc:ident, $env:ident, $parent:ident, $child:ident) => {
        if $parent.precedence() > $child.precedence() && $child.precedence() != Precedence::Closed {
            $child.pretty($alloc, $env).parens()
        } else {
            $child.pretty($alloc, $env)
        }
    };
    ($alloc:ident, $env:ident, $par_prec:expr, $child:ident) => {
        if $par_prec > $child.precedence() && $child.precedence() != Precedence::Closed {
            $child.pretty($alloc, $env).parens()
        } else {
            $child.pretty($alloc, $env)
        }
    };
}

impl Decl {
    pub fn pretty<'b, 'a: 'b, A: DocAllocator<'a>>(
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
        }
    }
}

impl Module {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
            .append(&self.name)
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

impl Scope {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
            .append(&self.name)
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

impl Signature {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
            .append(arg_list(alloc, env, &self.args))
            .append(
                self.retty.as_ref().map_or_else(
                    || alloc.nil(),
                    |t| alloc.text(" : ").append(t.pretty(alloc, env)),
                ),
            )
            .append(alloc.line_().append(self.contract.pretty(alloc, env))).nest(2)
            .group()
        // .append(alloc.line())
        // .append(self.contract.pretty(alloc, env).indent(2))
    }
}

impl Predicate {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("predicate ")
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" = ")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, env).indent(2))
    }
}

fn arg_list<'b: 'a, 'a, A: DocAllocator<'a>>(
    alloc: &'a A,
    env: &mut PrintEnv,
    args: &'a Vec<(LocalIdent, Type)>,
) -> DocBuilder<'a, A>
where
    A::Doc: Clone,
{
    if args.is_empty() {
        alloc.text("()")
    } else {
        alloc.intersperse(
            args.iter().map(|(id, ty)| {
                id.pretty(alloc, env).append(" : ").append(ty.pretty(alloc, env)).parens()
            }),
            alloc.space(),
        )
    }
}

impl Logic {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("let rec function ")
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" = ")))
            .group()
            .append(alloc.line())
            .append(self.body.pretty(alloc, env).indent(2))
    }
}

impl DeclClone {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let as_doc = match &self.as_nm {
            Some(nm) => alloc.text(" as ").append(nm),
            None => alloc.nil(),
        };
        let doc = alloc.text("clone ").append(self.name.pretty(alloc, env)).append(as_doc);

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

impl CloneSubst {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
        }
    }
}

impl Use {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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

impl Val {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc.text("val ").append(self.sig.pretty(alloc, env))
    }
}

impl Contract {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut doc = alloc.nil();
        env.in_logic = true;

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

        env.in_logic = false;
        doc
    }
}

impl LocalIdent {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        _: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        use LocalIdent::*;
        match self {
            Anon(id, Some(hmn)) => alloc.text(hmn).append("_").append(alloc.as_string(id)),
            Anon(id, None) => alloc.text("_").append(alloc.as_string(id)),
            Name(nm) => alloc.text(nm),
        }
    }
}

impl CfgFunction {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        alloc
            .text("let rec cfg ")
            .append(self.sig.pretty(alloc, env).append(alloc.line_()).append(alloc.text(" = ")))
            .group()
            .append(alloc.line())
            .append(sep_end_by(
                alloc,
                self.vars.iter().map(|(var, ty)| {
                    alloc
                        .text("var ")
                        .append(alloc.as_string(var))
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

impl Type {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
            TVar(v) => alloc.text(format!("'{}", v)),
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

impl Exp {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Exp::Current(box e) => alloc.text(" * ").append(e.pretty(alloc, env)),
            Exp::Final(box e) => alloc.text(" ^ ").append(e.pretty(alloc, env)),
            // TODO parenthesization
            Exp::Let { pattern, box arg, box body } => alloc
                .text("let ")
                .append(pattern.pretty(alloc, env))
                .append(" = ")
                .append(parens!(alloc, env, self, arg))
                .append(" in ")
                .append(body.pretty(alloc, env)),
            Exp::Var(v) => v.pretty(alloc, env),
            Exp::QVar(v) => v.pretty(alloc, env),
            Exp::RecUp { box record, label, box val } => alloc
                .space()
                .append(parens!(alloc, env, self, record))
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
                alloc.intersperse(args.iter().map(|a| a.pretty(alloc, env)), ", ").parens()
            }),

            Exp::BorrowMut(box exp) => {
                alloc.text("borrow_mut ").append(parens!(alloc, env, self, exp))
            }

            Exp::Const(c) => c.pretty(alloc, env),

            Exp::UnaryOp(UnOp::Not, box op) => alloc.text("not ").append(op.pretty(alloc, env)),

            Exp::UnaryOp(UnOp::Neg, box op) => alloc.text("- ").append(op.pretty(alloc, env)),

            Exp::BinaryOp(BinOp::Div, box l, box r) if env.in_logic => alloc
                .text("div ")
                .append(parens!(alloc, env, self, l))
                .append(" ")
                .append(parens!(alloc, env, self, r)),
            Exp::BinaryOp(op, box l, box r) => l
                .pretty(alloc, env)
                .append(alloc.space())
                .append(bin_op_to_string(op))
                .append(alloc.space())
                .append(r.pretty(alloc, env)),

            Exp::Call(box fun, args) => {
                parens!(alloc, env, self, fun).append(alloc.space()).append(
                    alloc.intersperse(
                        args.iter().map(|a| parens!(alloc, env, self, a)),
                        alloc.space(),
                    ),
                )
            }

            Exp::Verbatim(verb) => alloc.text(verb),

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
            Exp::Absurd => alloc.text("absurd"),
        }
    }
}

impl Statement {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
                .append(parens!(alloc, env, Precedence::Assign, rhs)),
            Statement::Invariant(nm, e) => {
                env.in_logic = true;
                let doc =
                    alloc.text("invariant ").append(alloc.text(nm)).append(alloc.space()).append(
                        alloc.space().append(e.pretty(alloc, env)).append(alloc.space()).braces(),
                    );
                env.in_logic = false;
                doc
            }
            Statement::Assume(assump) => {
                env.in_logic = true;
                let doc = alloc.text("assume ").append(
                    alloc.space().append(assump.pretty(alloc, env)).append(alloc.space()).braces(),
                );
                env.in_logic = false;
                doc
            }
            Statement::Assert(assert) => {
                env.in_logic = true;
                let doc = alloc.text("assert ").append(
                    alloc.space().append(assert.pretty(alloc, env)).append(alloc.space()).braces(),
                );
                env.in_logic = false;
                doc
            }
        }
    }
}

impl Terminator {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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

impl Pattern {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
                    doc = doc.append(
                        alloc
                            .intersperse(
                                pats.iter().map(|p| p.pretty(alloc, env)),
                                alloc.text(", "),
                            )
                            .parens(),
                    )
                }
                doc
            }
        }
    }
}

impl BlockId {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
    I::Item: Into<BuildDoc<'a, D::Doc, A>>,
    S: Into<BuildDoc<'a, D::Doc, A>> + Clone,
{
    let mut result = alloc.nil();
    let iter = docs.into_iter();

    for doc in iter {
        result = result.append(doc);
        result = result.append(separator.clone());
    }

    result
}

impl Block {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
        And => "&&",
        Or => "||",
        Add => "+",
        Sub => "-",
        Mul => "*",
        Div => "/",
        Eq => "=",
        Ne => "<>",
        Gt => ">",
        Ge => ">=",
        Lt => "<",
        Le => "<=",
    }
}

impl Constant {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        match self {
            Constant::Other(o) => alloc.text(o),
            Constant::Int(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc, env)).parens()
            }
            Constant::Int(i, None) => alloc.as_string(i),
            Constant::Uint(i, Some(t)) => {
                alloc.as_string(i).append(" : ").append(t.pretty(alloc, env)).parens()
            }
            Constant::Uint(i, None) => alloc.as_string(i),
        }
    }
}

impl TyDecl {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
        &'a self,
        alloc: &'a A,
        env: &mut PrintEnv,
    ) -> DocBuilder<'a, A>
    where
        A::Doc: Clone,
    {
        let mut ty_decl =
            alloc.text("type ").append(self.ty_name.pretty(alloc, env)).append(" ").append(
                alloc.intersperse(
                    self.ty_params.iter().map(|p| alloc.text(format!("'{}", p))),
                    alloc.space(),
                ),
            );

        if self.ty_constructors.len() > 0 {
            ty_decl = ty_decl.append(alloc.text(" = ").append(alloc.hardline()));
        }

        let mut inner_doc = alloc.nil();
        for (cons, args) in &self.ty_constructors {
            let mut ty_cons = alloc.text("| ").append(alloc.text(cons));

            if !args.is_empty() {
                ty_cons = ty_cons.append(
                    alloc
                        .intersperse(
                            args.iter().map(|ty_arg| ty_arg.pretty(alloc, env)),
                            alloc.text(", "),
                        )
                        .parens(),
                )
            }

            inner_doc = inner_doc.append(ty_cons.append(alloc.hardline()))
        }

        ty_decl.append(inner_doc.indent(2))
    }
}

impl QName {
    pub fn pretty<'b: 'a, 'a, A: DocAllocator<'a>>(
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
            .map(|t| alloc.text(t.clone()));

        alloc.intersperse(
            module_path.chain(std::iter::once(alloc.text(self.name()))),
            alloc.text("."),
        )
    }
}
