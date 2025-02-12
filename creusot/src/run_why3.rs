use crate::{
    backend::Why3Generator,
    options::{Options, Why3Sub},
};
use include_dir::{include_dir, Dir};
use rustc_ast::{
    mut_visit::DummyAstNode,
    ptr::P,
    token::{Lit, LitKind},
    Block, Expr, ExprKind, Pat, PatKind, PathSegment, Ty, TyKind, DUMMY_NODE_ID,
};
use rustc_ast_pretty::pprust::expr_to_string;
use rustc_span::{
    def_id::LocalDefId, source_map::dummy_spanned, symbol::Ident, BytePos, Span, Symbol,
    SyntaxContext, DUMMY_SP,
};
use serde_json::Deserializer;
use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::{Display, Formatter, Write},
    io::BufReader,
    path::PathBuf,
    process::{Command, Stdio},
};
use tempdir::TempDir;
use why3::ce_models::{ConcreteTerm, FunLitElt, Goal, Loc, ProverResult, TBool, Term, Why3Span};

static PRELUDE: Dir<'static> = include_dir!("$CARGO_MANIFEST_DIR/../prelude");

impl Display for Why3Sub {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Why3Sub::Prove => f.write_str("prove"),
            Why3Sub::Ide => f.write_str("ide"),
            Why3Sub::Replay => f.write_str("replay"),
        }
    }
}

pub(super) fn run_why3<'tcx>(ctx: &Why3Generator<'tcx>, file: Option<PathBuf>) {
    let Some(why3_cmd) = &ctx.opts.why3_cmd else { return };
    let Some(mut output_file) = file else {
        ctx.crash_and_error(DUMMY_SP, "cannot run why3 without file")
    };
    if matches!(why3_cmd.sub, Why3Sub::Replay) {
        output_file.set_extension("");
    }
    let temp_dir = TempDir::new("creusot_why3_prelude").expect("could not create temp dir");
    let mut prelude_dir: PathBuf = temp_dir.as_ref().into();
    prelude_dir.push("prelude");
    std::fs::create_dir(&prelude_dir).unwrap();

    PRELUDE.extract(&prelude_dir).expect("could extract prelude into temp dir");
    let mut command = Command::new(&why3_cmd.path);
    command
        .args([
            "-C",
            &why3_cmd.config_file.to_string_lossy(),
            "--warn-off=unused_variable",
            "--warn-off=clone_not_abstract",
            "--warn-off=axiom_abstract",
            "--debug=coma_no_trivial",
            &why3_cmd.sub.to_string(),
            "-L",
        ])
        .arg(temp_dir.path().as_os_str())
        .arg(&output_file)
        .args(why3_cmd.args.split_ascii_whitespace());

    if matches!(why3_cmd.sub, Why3Sub::Prove) {
        command.arg("--json");
        let span_map = &ctx.span_map.borrow();
        let mut child = command.stdout(Stdio::piped()).spawn().expect("could not run why3");
        let mut stdout = BufReader::new(child.stdout.take().unwrap());
        let de = Deserializer::from_reader(&mut stdout);
        for value in de.into_iter::<Goal>() {
            match value {
                Ok(x) => {
                    let ProverResult { answer, step, time, .. } = &x.prover_result;
                    if answer != "Valid" {
                        let span = span_map.decode_span(&x.term.loc);
                        let msg = format!(
                            "Prover reported {answer:?} (time: {time:?}, steps: {step:?}) when trying to solve goal {:?} {:?}",
                            x.term.goal_name, x.term.explanations
                        );
                        ctx.error(span.unwrap_or_default(), &msg).emit();
                        for model in x.prover_result.model_elems() {
                            let span = span_map.decode_span(&model.location);
                            let mut msg = format!("Model Element for {}\n", model.lsymbol.name);
                            if span.is_none() {
                                writeln!(msg, "Span: {:?}", &model.location).unwrap();
                            }
                            writeln!(msg, "Type: {:?}", model.value.value_type).unwrap();
                            let term = term_to_ast(&model.value.value_term);
                            writeln!(msg, "Term: {}", expr_to_string(&term)).unwrap();
                            let cterm = cterm_to_ast(&model.value.value_concrete_term);
                            writeln!(msg, "Concrete Term: {}", expr_to_string(&cterm)).unwrap();
                            ctx.dcx().span_note(span.unwrap_or_default(), msg)
                        }
                    }
                }
                Err(err) => {
                    let msg = format!("error parsing why3 output {err:?}");
                    ctx.error(DUMMY_SP, &msg).emit();
                }
            }
        }
        if !child.wait().expect("could not close why3").success() {
            ctx.crash_and_error(DUMMY_SP, "why3 did not exit successfully")
        };
    } else {
        command.status().expect("could not run why3");
        ctx.crash_and_error(DUMMY_SP, "did not run why3 prove")
    }
}

pub type SpanData = (SyntaxContext, Option<LocalDefId>);

#[derive(Debug, Default)]
pub struct SpanMap {
    vec: Vec<SpanData>,
    map: HashMap<SpanData, usize>,
}

impl SpanMap {
    fn encode_span_data(&mut self, s: SpanData) -> usize {
        let SpanMap { vec, map } = self;
        match map.entry(s) {
            Entry::Vacant(v) => {
                let i = vec.len();
                v.insert(i);
                vec.push(s);
                i
            }
            Entry::Occupied(o) => *o.get(),
        }
    }

    fn decode_span_data(&self, s: usize) -> SpanData {
        self.vec[s]
    }

    // TODO(xavier): Refactor this so that we don't check the why3_cmd when translating spans!!
    pub(crate) fn encode_span(
        &mut self,
        opts: &Options,
        span: Span,
    ) -> Option<why3::declaration::Attribute> {
        if let Some(cmd) = &opts.why3_cmd
            && matches!(cmd.sub, Why3Sub::Prove)
        {
            let data = span.data();
            Some(why3::declaration::Attribute::Span(
                "rustc_span".into(),
                data.lo.0 as usize,
                data.hi.0 as usize,
                self.encode_span_data((data.ctxt, data.parent)),
                0,
            ))
        } else {
            None
        }
    }

    fn decode_span(&self, loc: &Loc) -> Option<Span> {
        match loc {
            Loc::Span(Why3Span { file_name, start_line, start_char, end_line, .. })
                if file_name == "rustc_span" =>
            {
                let data = self.decode_span_data(*end_line as usize);
                Some(Span::new(BytePos(*start_line), BytePos(*start_char), data.0, data.1))
            }
            _ => None,
        }
    }
}

fn exp(kind: ExprKind) -> Expr {
    Expr { id: DUMMY_NODE_ID, kind, span: DUMMY_SP, attrs: Default::default(), tokens: None }
}

fn pat(kind: PatKind) -> Pat {
    Pat { id: DUMMY_NODE_ID, kind, span: DUMMY_SP, tokens: None }
}

fn ty(kind: TyKind) -> Ty {
    Ty { id: DUMMY_NODE_ID, kind, span: DUMMY_SP, tokens: None }
}

fn ident(name: &str) -> Ident {
    Ident { name: Symbol::intern(name), span: DUMMY_SP }
}

fn name_to_path(name: &str) -> Expr {
    let segments = name.split('.').map(|x| PathSegment::from_ident(ident(x))).collect();
    exp(ExprKind::Path(None, rustc_ast::Path { span: DUMMY_SP, segments, tokens: None }))
}

fn lit(name: &str, kind: LitKind, suffix: Option<&str>) -> Expr {
    exp(ExprKind::Lit(Lit {
        kind,
        symbol: Symbol::intern(name),
        suffix: suffix.map(Symbol::intern),
    }))
}

fn fun<'a>(args: impl IntoIterator<Item = &'a str>, body: Expr) -> Expr {
    exp(ExprKind::Closure(Box::new(rustc_ast::Closure {
        binder: rustc_ast::ClosureBinder::NotPresent,
        capture_clause: rustc_ast::CaptureBy::Ref,
        constness: rustc_ast::Const::No,
        movability: rustc_ast::Movability::Movable,
        fn_decl: P(rustc_ast::FnDecl {
            inputs: args
                .into_iter()
                .map(|x| rustc_ast::Param {
                    attrs: Default::default(),
                    ty: P(ty(TyKind::Infer)),
                    pat: P(pat(PatKind::Ident(rustc_ast::BindingMode::NONE, ident(x), None))),
                    id: DUMMY_NODE_ID,
                    span: DUMMY_SP,
                    is_placeholder: false,
                })
                .collect(),
            output: rustc_ast::FnRetTy::Default(DUMMY_SP),
        }),
        body: P(body),
        fn_decl_span: DUMMY_SP,
        fn_arg_span: DUMMY_SP,
        coroutine_kind: None,
    })))
}

fn app(f: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    let mut v: Vec<_> = args.into_iter().map(P).collect();

    let take = |x: &mut P<Expr>| std::mem::replace(&mut **x, Expr::dummy());
    match (f, &mut *v) {
        ("(=)" | "=", [t1, t2]) => binop("=", [t1, t2].map(take)),
        _ => exp(ExprKind::Call(P(name_to_path(f)), v.into())),
    }
}

fn block(exp: Expr) -> Block {
    let stmt = rustc_ast::Stmt {
        id: DUMMY_NODE_ID,
        kind: rustc_ast::StmtKind::Expr(P(exp)),
        span: DUMMY_SP,
    };
    Block {
        stmts: [stmt].into_iter().collect(),
        id: DUMMY_NODE_ID,
        rules: rustc_ast::BlockCheckMode::Default,
        span: Default::default(),
        tokens: None,
        could_be_bare_literal: false,
    }
}
fn ite([ift, then, elset]: [Expr; 3]) -> Expr {
    let elset = match elset.kind {
        ExprKind::If(..) => elset,
        _ => exp(ExprKind::Block(P(block(elset)), None)),
    };

    exp(ExprKind::If(P(ift), P(block(then)), Some(P(elset))))
}

fn binop(op: &str, [t1, t2]: [Expr; 2]) -> Expr {
    use rustc_ast::BinOpKind::*;
    let op = match op {
        "+" => Add,
        "-" => Sub,
        "*" => Mul,
        "=" => Eq,
        "==" => Eq,
        "/" => Div,
        "&&" => And,
        "/\\" => And,
        "||" => Or,
        "\\/" => Or,
        "And" => And,
        "Tand" => And,
        "Or" => Or,
        "Tor" => Or,
        _ => {
            warn!("unsupported Binop {op}");
            BitXor
        }
    };
    exp(ExprKind::Binary(dummy_spanned(op), P(t1), P(t2)))
}

fn not(t: Expr) -> Expr {
    let op = rustc_ast::UnOp::Not;
    exp(ExprKind::Unary(op, P(t)))
}

fn term_to_ast(t: &Term) -> Expr {
    match t {
        Term::Var(v) => name_to_path(&v.vs_name),
        Term::Const { ty: _ty, val } => lit(val, LitKind::Integer, None),
        Term::App { ls, args } => app(ls, args.iter().map(term_to_ast)),
        Term::If { ift, then, elset } => ite([ift, then, elset].map(|x| term_to_ast(x))),
        Term::Eps { vs, t } => app("eps!", [fun([&*vs.vs_name], term_to_ast(t))]),
        Term::Fun { args, body } => fun(args.iter().map(|x| &*x.vs_name), term_to_ast(body)),
        Term::Quant { quant, vs, t } => {
            app(quant, [fun(vs.iter().map(|x| &*x.vs_name), term_to_ast(t))])
        }
        Term::Binop { binop: op, t1, t2 } => binop(op, [t1, t2].map(|x| term_to_ast(x))),
        Term::Not(t) => not(term_to_ast(t)),
        Term::Let(x) => app("let!", [name_to_path(x)]),
        Term::Case(x) => app("case!", [name_to_path(x)]),
        Term::Bool(TBool::True) => lit("true", LitKind::Bool, None),
        Term::Bool(TBool::False) => lit("false", LitKind::Bool, None),
        _ => lit(&format!("{t:?}"), LitKind::Str, None),
    }
}

fn fun_lit_elt_to_ast(elt: &FunLitElt) -> P<Expr> {
    P(exp(ExprKind::Tup(
        [&elt.indice, &elt.value].into_iter().map(|x| P(cterm_to_ast(x))).collect(),
    )))
}

fn cterm_to_ast(t: &ConcreteTerm) -> Expr {
    match t {
        ConcreteTerm::Var(v) => name_to_path(v),
        ConcreteTerm::Integer(n) => lit(&n.int_value, LitKind::Integer, None),
        ConcreteTerm::Boolean(b) => lit(&b.to_string(), LitKind::Bool, None),
        ConcreteTerm::App { ls, args } => app(ls, args.iter().map(cterm_to_ast)),
        ConcreteTerm::If { ift, then, elset } => ite([ift, then, elset].map(|x| cterm_to_ast(x))),
        ConcreteTerm::String(s) => lit(&format!("{s:?}"), LitKind::Str, None),
        ConcreteTerm::Eps { var, t } => app("eps!", [fun([&**var], cterm_to_ast(t))]),
        ConcreteTerm::Fun { args, body } => fun(args.iter().map(|x| &**x), cterm_to_ast(body)),
        ConcreteTerm::Quant { quant, vs, t } => {
            app(quant, [fun(vs.iter().map(|x| &**x), cterm_to_ast(t))])
        }
        ConcreteTerm::Binop { binop: op, t1, t2 } => binop(op, [t1, t2].map(|x| cterm_to_ast(x))),
        ConcreteTerm::Not(t) => not(cterm_to_ast(t)),
        ConcreteTerm::FunctionLiteral { elts, other } => {
            let arr = exp(ExprKind::Array(elts.iter().map(fun_lit_elt_to_ast).collect()));
            app("funlit!", [arr, cterm_to_ast(other)])
        }
        ConcreteTerm::Proj { name, value } => match (&**name, &**value) {
            ("prelude.prelude.UInt8.uint8'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("u8"))
            }
            ("prelude.prelude.UInt16.uint16'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("u16"))
            }
            ("mach.int.UInt32Gen.uint32'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("u32"))
            }
            ("mach.int.UInt64Gen.uint64'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("u64"))
            }
            ("prelude.prelude.UInt128.uint16'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("u128"))
            }
            ("prelude.prelude.Int8.int8'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("i8"))
            }
            ("prelude.prelude.Int16.int16'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("i16"))
            }
            ("mach.int.Int32.int32'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("i32"))
            }
            ("mach.int.Int64.int64'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("i64"))
            }
            ("prelude.prelude.Int128.int128'int", ConcreteTerm::Integer(n)) => {
                lit(&n.int_value, LitKind::Integer, Some("i128"))
            }
            _ => app("proj!", [name_to_path(name), cterm_to_ast(value)]),
        },
        _ => lit(&format!("{t:?}"), LitKind::Str, None),
    }
}
