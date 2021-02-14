use std::fmt;

use super::*;

/// Original code from https://github.com/digama0/mm0/ (CC-0)
/// The side information required to print an object in the environment.

#[derive(Copy, Clone, Debug)]
pub struct FormatEnv<'a> {
    /// Currently open scopes.
    pub scope: &'a [String],
    /// Indentation to prefix lines with
    pub indent: usize,
}

/// A trait for displaying data given access to the environment.
pub trait EnvDisplay {
    /// Print formatted output to the given formatter. The signature is exactly the same
    /// as [`Display::fmt`] except it has an extra argument for the environment.
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<'a> Default for FormatEnv<'a> {
    fn default() -> Self {
        FormatEnv { scope: &[], indent: 0 }
    }
}

/// The result of [`FormatEnv::to`], a struct that implements [`Display`] if the
/// argument implements [`EnvDisplay`].
pub struct Print<'a, D: ?Sized> {
    fe: FormatEnv<'a>,
    e: &'a D,
}

impl<'a> FormatEnv<'a> {
    /// Given a [`FormatEnv`], convert an `impl EnvDisplay` into an `impl Display`.
    /// This can be used in macros like `println!("{}", fe.to(e))` to print objects.
    pub fn to<D: ?Sized>(self, e: &'a D) -> Print<'a, D> {
        Print { fe: self, e }
    }

    pub fn indent<F>(mut self, i: usize, mut f: F) -> std::fmt::Result
    where
        F: FnMut(Self) -> std::fmt::Result,
    {
        self.indent += i;
        f(self)
    }

    // Print the correct indentation for this line
    pub fn indent_line(self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:indent$}", "", indent = self.indent)
    }
}

impl<'a, D: EnvDisplay + ?Sized> fmt::Display for Print<'a, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.e.fmt(self.fe, f)
    }
}

use itertools::*;

// FIXME: Doesn't take into account associativity when deciding when to put parens
macro_rules! parens {
    ($fe:ident, $parent:ident, $child:ident) => {
        if $parent.precedence() > $child.precedence() && $child.precedence() != Precedence::Closed {
            format!("({})", $fe.to($child))
        } else {
            format!("{}", $fe.to($child))
        }
    };
    ($fe:ident, $par_prec:expr, $child:ident) => {
        if $par_prec > $child.precedence() && $child.precedence() != Precedence::Closed {
            format!("({})", $fe.to($child))
        } else {
            format!("{}", $fe.to($child))
        }
    };
}

impl EnvDisplay for Decl {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decl::FunDecl(fun) => writeln!(f, "{}", fe.to(fun)),
            // Decl::TyDecl(t) => { writeln!(f, "{}", fe.to(t)) }
            // Decl::PredDecl(p) => { writeln!(f, "{}", fe.to(p)) }
        }
    }
}

impl EnvDisplay for Predicate {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fe.indent_line(f)?;

        write!(f, "predicate {} ", fe.to(&self.name))?;

        if self.args.is_empty() {
            write!(f, "() ")?;
        } else {
            for (nm, ty) in &self.args {
                write!(f, "({} : {}) ", nm, fe.to(ty))?;
            }
        }

        writeln!(f, "=")?;
        fe.indent(2, |fe| {
            fe.indent_line(f)?;
            write!(f, "{}", fe.to(&self.body))
        })?;

        Ok(())
    }
}

impl EnvDisplay for Function {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fe.indent_line(f)?;
        write!(f, "let rec cfg {} ", fe.to(&self.name))?;

        if self.args.is_empty() {
            write!(f, "()")?;
        }

        for (nm, ty) in &self.args {
            write!(f, "(o_{} : {})", nm, fe.to(ty))?;
        }

        writeln!(f, " : {}", fe.to(&self.retty))?;

        fe.indent(2, |fe| {
            for req in &self.preconds {
                fe.indent_line(f)?;
                writeln!(f, "requires {{ {} }}", req)?;
            }

            for req in &self.postconds {
                fe.indent_line(f)?;
                writeln!(f, "ensures {{ {} }}", req)?;
            }
            fe.indent_line(f)?;
            writeln!(f, "=")?;

            Ok(())
        })?;

        // Forward declare all arguments
        fe.indent_line(f)?;
        writeln!(f, "var _0 : {};", fe.to(&self.retty))?;

        for (var, ty) in self.args.iter() {
            fe.indent_line(f)?;
            writeln!(f, "var {} : {};", var, fe.to(ty))?;
        }

        // Forward declare all variables
        for (var, ty) in self.vars.iter() {
            fe.indent_line(f)?;
            writeln!(f, "var {} : {};", var, fe.to(ty))?;
        }

        fe.indent_line(f)?;
        writeln!(f, "{{")?;
        fe.indent(2, |fe| {
            for (arg, _) in self.args.iter() {
                fe.indent_line(f)?;
                writeln!(f, "{} <- o_{};", arg, arg)?;
            }

            fe.indent_line(f)?;
            writeln!(f, "goto BB0")
        })?;

        fe.indent_line(f)?;
        writeln!(f, "}}")?;

        for (id, block) in &self.blocks {
            fe.indent_line(f)?;
            write!(f, "{} {}", id, fe.to(block))?;
        }

        Ok(())
    }
}

impl EnvDisplay for Type {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Type::*;

        macro_rules! ty_parens {
            ($fe:ident, $e:ident) => {
                if $e.complex() {
                    format!("({})", $fe.to($e))
                } else {
                    format!("{}", $fe.to($e))
                }
            };
        }

        match self {
            Bool => {
                write!(f, "bool")?;
            }
            Char => {
                write!(f, "char")?;
            }
            Int(size) => {
                use rustc_ast::ast::IntTy::*;
                match size {
                    I8 => write!(f, "int8"),
                    I16 => write!(f, "int16"),
                    I32 => write!(f, "int32"),
                    I64 => write!(f, "int64"),
                    I128 => write!(f, "int128"),
                    Isize => write!(f, "isize"),
                }?
            }
            Uint(size) => {
                use rustc_ast::ast::UintTy::*;
                match size {
                    U8 => write!(f, "uint8"),
                    U16 => write!(f, "uint16"),
                    U32 => write!(f, "uint32"),
                    U64 => write!(f, "uint64"),
                    U128 => write!(f, "uint128"),
                    Usize => write!(f, "usize"),
                }?
            }
            Float(size) => {
                use rustc_ast::ast::FloatTy::*;
                match size {
                    F32 => write!(f, "single"),
                    F64 => write!(f, "double"),
                }?
            }
            MutableBorrow(box t) => {
                write!(f, "borrowed {}", ty_parens!(fe, t))?;
            }
            TVar(v) => {
                write!(f, "{}", v)?;
            }
            TFun(box a, box b) => {
                write!(f, "{} -> {}", ty_parens!(fe, a), ty_parens!(fe, b))?;
            }
            TConstructor(ty) => {
                write!(f, "{}", fe.to(ty))?;
            }
            TApp(box tyf, args) => {
                if args.is_empty() {
                    tyf.fmt(fe, f)?;
                } else {
                    write!(
                        f,
                        "{} {}",
                        fe.to(tyf),
                        args.iter().format_with(" ", |elt, f| {
                            f(&ty_parens!(fe, elt))
                            // f(&format_args!("{}", ty_parens!(fe, elt)))
                        })
                    )?;
                }
            }
            Tuple(tys) => {
                write!(f, "({})", tys.iter().format_with(", ", |elt, f| { f(&format_args!("{}", fe.to(elt))) }))?;
            }
        }

        Ok(())
    }
}

impl EnvDisplay for Exp {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Exp::Current(box e) => {
                write!(f, " * {}", fe.to(e))?;
            }
            Exp::Final(box e) => {
                write!(f, " ^ {}", fe.to(e))?;
            }
            Exp::Let { pattern, box arg, box body } => {
                write!(f, "let {} = {} in {}", fe.to(pattern), parens!(fe, self, arg), parens!(fe, self, body))?;
            }
            Exp::Var(v) => {
                write!(f, "{}", v)?;
            }
            Exp::QVar(v) => {
                write!(f, "{}", fe.to(v))?;
            }
            Exp::RecUp { box record, label, box val } => {
                write!(f, "{{ {} with {} = {} }}", parens!(fe, self, record), label, parens!(fe, self, val))?;
            }
            Exp::Tuple(vs) => {
                write!(f, "({})", vs.iter().format_with(", ", |elt, f| { f(&fe.to(elt)) }))?;
            }
            Exp::Constructor { ctor, args } => {
                if args.is_empty() {
                    EnvDisplay::fmt(ctor, fe, f)?;
                } else {
                    write!(f, "{}({})", fe.to(ctor), args.iter().format_with(", ", |elt, f| { f(&fe.to(elt)) }))?;
                }
            }
            Exp::BorrowMut(box exp) => {
                write!(f, "borrow_mut {}", parens!(fe, self, exp))?;
            }
            Exp::Const(c) => {
                write!(f, "{}", c)?;
            }
            Exp::UnaryOp(UnOp::Not, box op) => {
                write!(f, "not {}", parens!(fe, self, op))?;
            }
            Exp::UnaryOp(UnOp::Neg, box op) => {
                write!(f, "- {}", parens!(fe, self, op))?;
            }
            Exp::BinaryOp(FullBinOp::Other(BinOp::Div), box l, box r) => {
                write!(f, "div {} {}", parens!(fe, self, l), parens!(fe, self, r))?;
            }
            Exp::BinaryOp(op, box l, box r) => {
                write!(f, "{} {} {}", parens!(fe, self, l), bin_op_to_string(op), parens!(fe, self, r))?;
            }
            Exp::Call(box fun, args) => {
                write!(f, "{} {}", parens!(fe, self, fun), args.iter().map(|a| parens!(fe, self, a)).format(" "))?;
            }
            Exp::Verbatim(verb) => {
                write!(f, "{}", verb)?;
            }
            Exp::Abs(ident, box body) => {
                write!(f, "fun {} -> {}", ident, fe.to(body))?;
            }
            Exp::Match(box scrut, brs) => {
                writeln!(f, "match ({}) with", fe.to(scrut))?;
                fe.indent(2, |fe| {
                    for (pat, tgt) in brs {
                        fe.indent_line(f)?;
                        writeln!(f, "| {} -> {}", fe.to(pat), fe.to(tgt))?;
                    }
                    fe.indent_line(f)?;
                    writeln!(f, "end")
                })?;
            }
            Exp::Forall(binders, box exp) => {
                write!(f, "forall ")?;

                let binder_fmt =
                    binders.iter().format_with(", ", |(l, ty), f| f(&format_args!("{} : {}", l, fe.to(ty))));

                write!(f, "{} . {}", binder_fmt, fe.to(exp))?;
            }
            Exp::Exists(binders, box exp) => {
                write!(f, "exists ")?;

                for (l, ty) in binders {
                    write!(f, "({} : {}) ", l, fe.to(ty))?;
                }

                write!(f, ". {}", fe.to(exp))?;
            }
            Exp::Impl(box hyp, box exp) => {
                write!(f, "{} -> {}", parens!(fe, self, hyp), parens!(fe, self, exp))?;
            }
        }
        Ok(())
    }
}

impl EnvDisplay for Statement {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Assign { lhs, rhs } => {
                write!(f, "{} <- {}", lhs, parens!(fe, Precedence::Assign, rhs))?;
            }
            Statement::Invariant(nm, e) => {
                write!(f, "invariant {} {{ {} }}", nm, fe.to(e))?;
            }
            Statement::Assume(assump) => {
                write!(f, "assume {{ {} }}", fe.to(assump))?;
            }
        }
        Ok(())
    }
}

impl EnvDisplay for Terminator {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Terminator::*;
        match self {
            Goto(tgt) => {
                writeln!(f, "goto {}", tgt)?;
            }
            Absurd => {
                writeln!(f, "absurd")?;
            }
            Return => {
                writeln!(f, "return _0")?;
            }
            Switch(discr, brs) => {
                writeln!(f, "switch ({})", fe.to(discr))?;
                fe.indent(2, |fe| {
                    for (pat, tgt) in brs {
                        fe.indent_line(f)?;
                        write!(f, "| {} -> {}", fe.to(pat), fe.to(tgt))?;
                    }
                    fe.indent_line(f)?;
                    writeln!(f, "end")
                })?;
            }
        }
        Ok(())
    }
}

impl EnvDisplay for Pattern {
    fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Wildcard => {
                write!(f, "_")?;
            }
            Pattern::VarP(v) => {
                write!(f, "{}", v)?;
            }
            Pattern::TupleP(vs) => {
                write!(f, "({})", vs.iter().map(|x| fe.to(x)).format(", "))?;
            }
            Pattern::ConsP(c, pats) => {
                if pats.is_empty() {
                    write!(f, "{}", fe.to(c))?;
                } else {
                    write!(f, "{}({})", fe.to(c), pats.iter().map(|p| fe.to(p)).format(", "))?;
                }
            }
            Pattern::LitP(lit) => {
                write!(f, "{}", lit)?;
            }
        }
        Ok(())
    }
}

impl Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BB{}", self.0)
    }
}

impl EnvDisplay for Block {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;

        fe.indent(2, |fe| {
            for stmt in &self.statements {
                fe.indent_line(f)?;
                writeln!(f, "{};", fe.to(stmt))?;
            }

            fe.indent_line(f)?;
            self.terminator.fmt(fe, f)
        })?;

        fe.indent_line(f)?;
        writeln!(f, "}}")?;

        Ok(())
    }
}

fn bin_op_to_string(op: &FullBinOp) -> &str {
    use rustc_middle::mir::BinOp::*;
    use FullBinOp::*;
    match op {
        And => "&&",
        Or => "||",
        Other(Add) => "+",
        Other(Sub) => "-",
        Other(Mul) => "*",
        Other(Eq) => "=",
        Other(Ne) => "<>",
        Other(Gt) => ">",
        Other(Ge) => ">=",
        Other(Lt) => "<",
        Other(Le) => "<=",
        _ => unreachable!("unexpected bin-op"),
    }
}

impl Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Other(o) => write!(f, "{}", o),
            Constant::Int(i) => write!(f, "{}", i),
            Constant::Uint(u) => write!(f, "{}", u), // Constant::Float(flt) => { write!(f, "{}", flt) }
        }
    }
}

impl EnvDisplay for TyDecl {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fe.indent_line(f)?;
        writeln!(f, "type {} {} =", fe.to(&self.ty_name), self.ty_params.iter().format(" "))?;

        fe.indent(2, |fe| {
            for (cons, args) in self.ty_constructors.iter() {
                fe.indent_line(f)?;
                if args.is_empty() {
                    writeln!(f, "  | {}", cons)?;
                } else {
                    writeln!(f, "  | {}({})", cons, args.iter().format_with(", ", |elt, f| { f(&fe.to(elt)) }))?;
                }
            }
            Ok(())
        })?;

        Ok(())
    }
}

impl EnvDisplay for QName {
    fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use itertools::EitherOrBoth::*;
        // Strip the shared prefix between currently open scope and the identifier we are printing
        let module_path = format!(
            "{}",
            fe.scope
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
                .format(".")
        );

        if module_path == "" {
            write!(f, "{}", self.name())
        } else {
            write!(f, "{}.{}", module_path, self.name())
        }
    }
}
