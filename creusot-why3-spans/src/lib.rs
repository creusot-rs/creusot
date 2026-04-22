//! vc-spans — extract source spans of unproved proof goals from why3 .coma files.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};

use ocaml_interop::{ocaml, OCamlRuntime, ToOCaml};
use quick_xml::events::Event;
use quick_xml::reader::Reader;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    pub file: String,
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

impl Location {
    fn display(&self) -> String {
        if self.start_line == self.end_line {
            format!("{}:{}:{}-{}", self.file, self.start_line, self.start_col, self.end_col)
        } else {
            format!("{}:{}:{}-{}:{}", self.file, self.start_line, self.start_col, self.end_line, self.end_col)
        }
    }
}

/// The kind of a proof obligation, with kind-specific data attached.
#[derive(Debug, Clone)]
pub enum GoalKind {
    Assertion,
    Overflow,
    Panic,
    /// Invariant failed to be established before the loop.
    LoopInvariantEstablish,
    /// Invariant failed to be preserved by the loop body.
    LoopInvariantPreserve,
    LoopVariant,
    /// `definition` is the location of the `requires` clause.
    Precondition { definition: Location },
    Postcondition,
    /// `definition` is the location where the law is declared.
    Law { definition: Location },
    /// Trait contract refinement: the implementation does not satisfy the
    /// contract declared on the trait. `trait_location` is the span of the
    /// trait contract that was not satisfied.
    Refinement { trait_location: Option<Location> },
    /// A type invariant (from the `Invariant` trait) could not be proved.
    /// `definition` is the location of the `invariant` method body.
    TypeInvariant { definition: Option<Location> },
    Other,
}

impl GoalKind {
    fn label(&self) -> &'static str {
        match self {
            GoalKind::Assertion               => "assertion",
            GoalKind::Overflow                => "overflow",
            GoalKind::Panic                   => "panic",
            GoalKind::LoopInvariantEstablish  => "loop_invariant",
            GoalKind::LoopInvariantPreserve   => "loop_invariant",
            GoalKind::LoopVariant             => "loop_variant",
            GoalKind::Precondition { .. }     => "precondition",
            GoalKind::Postcondition           => "postcondition",
            GoalKind::Law { .. }              => "law",
            GoalKind::Refinement { .. }        => "refinement",
            GoalKind::TypeInvariant { .. }       => "type_invariant",
            GoalKind::Other                    => "other",
        }
    }
}

/// A resolved, display-ready unproved goal.
///
/// For `GoalKind::Precondition` and `GoalKind::Law`, `location` is the **call
/// site** (the most actionable location for the user), and the `definition`
/// field inside the variant holds the clause/law declaration location.
#[derive(Debug, Clone)]
pub struct Goal {
    /// Human-readable function name (without the `vc_` prefix and index suffix).
    pub function_name: String,
    /// The kind of proof obligation, with kind-specific data.
    pub kind: GoalKind,
    /// Explanation string from the VC (e.g. "loop invariant #0").
    pub expl: String,
    /// Primary location: the call site for preconditions/laws, otherwise the VC location.
    pub location: Location,
}

#[derive(Debug, Clone)]
struct VcSpan {
    name: String,
    expl: String,
    kind: String,
    file: String,
    start_line: i64,
    start_col:  i64,
    end_line:   i64,
    end_col:    i64,
    file2: String,
    start_line2: i64,
    start_col2:  i64,
    end_line2:   i64,
    end_col2:    i64,
    coma_ref: String,
    coma_l1:  i64,
    coma_c1:  i64,
    coma_l2:  i64,
    coma_c2:  i64,
}

impl VcSpan {
    fn has_source_location(&self) -> bool { !self.file.is_empty() }
    fn has_source_location2(&self) -> bool { !self.file2.is_empty() }
    fn has_coma_ref(&self) -> bool { !self.coma_ref.is_empty() }

    fn function_name(&self) -> &str {
        let s = self.name.strip_prefix("vc_").unwrap_or(&self.name);
        if let Some(dot) = s.find('.') { &s[..dot] } else { s }
    }

    fn location(&self) -> Option<Location> {
        if !self.has_source_location() { return None; }
        Some(Location {
            file:       self.file.clone(),
            start_line: self.start_line as usize,
            start_col:  self.start_col as usize,
            end_line:   self.end_line as usize,
            end_col:    self.end_col as usize,
        })
    }

    fn location2(&self) -> Option<Location> {
        if !self.has_source_location2() { return None; }
        Some(Location {
            file:       self.file2.clone(),
            start_line: self.start_line2 as usize,
            start_col:  self.start_col2 as usize,
            end_line:   self.end_line2 as usize,
            end_col:    self.end_col2 as usize,
        })
    }
}

fn parse_spans(s: &str) -> Result<Vec<VcSpan>, GoalError> {
    if s.starts_with("error: ") { return Err(GoalError::Stub(s[7..].to_owned())); }
    if s.is_empty() { return Ok(Vec::new()); }
    let mut spans = Vec::new();
    for record in s.split("\n---\n") {
        let lines: Vec<&str> = record.splitn(18, '\n').collect();
        if lines.len() != 18 {
            return Err(GoalError::MalformedRecord { num_lines: lines.len(), record: record.to_owned() });
        }
        let pi = |s: &str| -> Result<i64, GoalError> {
            s.parse::<i64>().map_err(|e| GoalError::InvalidInt(e))
        };
        spans.push(VcSpan {
            name:        lines[0].to_owned(),
            expl:        lines[1].to_owned(),
            kind:        lines[2].to_owned(),
            file:        lines[3].to_owned(),
            start_line:  pi(lines[4])?,
            start_col:   pi(lines[5])?,
            end_line:    pi(lines[6])?,
            end_col:     pi(lines[7])?,
            file2:       lines[8].to_owned(),
            start_line2: pi(lines[9])?,
            start_col2:  pi(lines[10])?,
            end_line2:   pi(lines[11])?,
            end_col2:    pi(lines[12])?,
            coma_ref:    lines[13].to_owned(),
            coma_l1:     pi(lines[14])?,
            coma_c1:     pi(lines[15])?,
            coma_l2:     pi(lines[16])?,
            coma_c2:     pi(lines[17])?,
        });
    }
    Ok(spans)
}

fn session_path(coma_file: &Path) -> PathBuf {
    let stem = coma_file.file_stem().unwrap_or_default();
    let dir  = coma_file.parent().unwrap_or(Path::new("."));
    dir.join(stem).join("why3session.xml")
}

fn unproved_leaf_goals(session: PathBuf) -> Result<HashSet<String>, GoalError> {
    let content = match std::fs::read_to_string(&session) {
        Ok(content) => content,
        Err(error) => return Err(GoalError::ReadSessionFile { path: session, error }),
    };

    let mut reader = Reader::from_str(&content);
    reader.config_mut().trim_text(true);

    let mut stack: Vec<(String, bool, bool)> = Vec::new();
    let mut out: HashSet<String> = HashSet::new();
    let mut buf = Vec::new();

    loop {
        match reader.read_event_into(&mut buf) {
            Ok(Event::Start(e)) if e.name().as_ref() == b"goal" => {
                let name   = attr_str(&e, b"name").unwrap_or_default();
                let proved = attr_str(&e, b"proved").map_or(false, |v| v == "true");
                if let Some(parent) = stack.last_mut() { parent.2 = true; }
                stack.push((name, proved, false));
            }
            Ok(Event::Empty(e)) if e.name().as_ref() == b"goal" => {
                let name   = attr_str(&e, b"name").unwrap_or_default();
                let proved = attr_str(&e, b"proved").map_or(false, |v| v == "true");
                if let Some(parent) = stack.last_mut() { parent.2 = true; }
                if !proved { out.insert(name); }
            }
            Ok(Event::End(e)) if e.name().as_ref() == b"goal" => {
                if let Some((name, proved, has_sub)) = stack.pop() {
                    if !proved && !has_sub { out.insert(name); }
                }
            }
            Ok(Event::Eof) => break,
            Err(error) => return Err(GoalError::ParseXML { path: session, error }),
            _ => {}
        }
        buf.clear();
    }

    Ok(out)
}

fn attr_str(e: &quick_xml::events::BytesStart, name: &[u8]) -> Option<String> {
    e.attributes()
        .filter_map(|a| a.ok())
        .find(|a| a.key.as_ref() == name)
        .and_then(|a| String::from_utf8(a.value.into_owned()).ok())
}

/// Parse the first-line span comment from a coma file:
/// `(* #"/path/to/file.rs" l1 c1 l2 c2 *)`
fn coma_header_location(coma_file: &Path) -> Option<Location> {
    use std::io::{BufRead, BufReader};
    let f = std::fs::File::open(coma_file).ok()?;
    let first = BufReader::new(f).lines().next()?.ok()?;
    // Expected format: (* #"<file>" <l1> <c1> <l2> <c2> *)
    let inner = first.strip_prefix("(* #\"")?.strip_suffix(" *)")?;
    let (file, rest) = inner.split_once('"')?;
    let nums: Vec<i64> = rest.split_whitespace()
        .filter_map(|s| s.parse().ok())
        .collect();
    if nums.len() < 4 { return None; }
    Some(Location {
        file:       file.to_string(),
        start_line: nums[0] as usize,
        start_col:  nums[1] as usize,
        end_line:   nums[2] as usize,
        end_col:    nums[3] as usize,
    })
}

type ComaCache = HashMap<String, Vec<VcSpan>>;

fn resolve_cross_ref(cr: &mut OCamlRuntime, span: &VcSpan, cache: &mut ComaCache) -> Option<Location> {
    if !span.has_coma_ref() { return None; }
    let coma_ref = &span.coma_ref;
    let ref_spans = cache.entry(coma_ref.clone()).or_insert_with(|| {
        let coma_ref = coma_ref.to_boxroot(cr);
        parse_spans(vc_spans_extract(cr, &coma_ref).get(cr).as_str()).unwrap_or_default()
    });
    for rs in &*ref_spans {
        if rs.has_source_location() && rs.coma_ref == *coma_ref
            && rs.coma_l1 == span.coma_l1 && rs.coma_c1 == span.coma_c1
        {
            return rs.location();
        }
    }
    for rs in &*ref_spans {
        if rs.has_source_location() && rs.coma_l1 == span.coma_l1 {
            return rs.location();
        }
    }
    None
}

fn span_matches_unproved(name: &str, unproved: &HashSet<String>) -> bool {
    if unproved.contains(name) { return true; }
    let prefix = format!("{}.", name);
    if unproved.iter().any(|leaf| leaf.starts_with(&prefix)) { return true; }
    unproved.iter().any(|leaf| name.starts_with(&format!("{}.", leaf)))
}

/// Returns the last dot-separated component of a goal name as a usize, if present.
fn last_name_index(name: &str) -> Option<usize> {
    name.rsplit_once('.')
        .and_then(|(_, last)| last.parse::<usize>().ok())
}

fn parse_kind(span: &VcSpan) -> GoalKind {
    let fallback_loc = || Location {
        file:       span.file.clone(),
        start_line: span.start_line as usize,
        start_col:  span.start_col as usize,
        end_line:   span.end_line as usize,
        end_col:    span.end_col as usize,
    };
    match span.kind.as_str() {
        "assertion"      => GoalKind::Assertion,
        "overflow"       => GoalKind::Overflow,
        "panic"          => GoalKind::Panic,
        "loop_invariant" => {
            // split_vc always produces two sub-goals for a loop invariant:
            // index 0 = establish (before the loop), index 1 = preserve (loop body).
            match last_name_index(&span.name) {
                Some(0) => GoalKind::LoopInvariantEstablish,
                Some(1) => GoalKind::LoopInvariantPreserve,
                // Deeper nesting (e.g. .0.0) — use the grandparent index.
                _ => match span.name.rsplit_once('.')
                        .and_then(|(parent, _)| last_name_index(parent))
                    {
                        Some(0) => GoalKind::LoopInvariantEstablish,
                        _       => GoalKind::LoopInvariantPreserve,
                    }
            }
        }
        "loop_variant"   => GoalKind::LoopVariant,
        "postcondition"  => GoalKind::Postcondition,
        "law"            => GoalKind::Law {
            definition: span.location2().unwrap_or_else(fallback_loc),
        },
        "type_invariant" => GoalKind::TypeInvariant {
            definition: span.location2(),
        },
        "refinement"     => GoalKind::Refinement { trait_location: None },
        "precondition"   => GoalKind::Precondition {
            definition: span.location().unwrap_or_else(fallback_loc),
        },
        _                => GoalKind::Other,
    }
}

fn collect_unproved_goals(
    cr: &mut OCamlRuntime,
    coma_file: &Path,
    all_spans: &[VcSpan],
    show_all: bool,
    debug: bool,
    coma_cache: &mut ComaCache,
    goals: &mut Vec<Result<Goal, GoalError>>,
) {
    let unproved_set: Option<HashSet<String>> = if show_all {
        None
    } else {
        let session = session_path(coma_file);
        match unproved_leaf_goals(session) {
            Ok(unproved_set) => Some(unproved_set),
            Err(error) => {
                goals.push(Err(error));
                return
            }
        }
    };

    if debug {
        eprintln!("[debug] span names from stub ({}):", all_spans.len());
        for s in all_spans {
            eprintln!("  span: {:?} kind={:?} expl={:?} file2={:?}", s.name, s.kind, s.expl, s.file2);
        }
        if let Some(ref set) = unproved_set {
            let mut v: Vec<_> = set.iter().collect();
            v.sort();
            eprintln!("[debug] unproved leaves from session ({}):", v.len());
            for n in &v { eprintln!("  leaf: {:?}", n); }
        }
    }

    let mut seen_display: HashSet<String> = HashSet::new();

    for span in all_spans {
        let matches = match &unproved_set {
            None      => true,
            Some(set) => span_matches_unproved(&span.name, set),
        };
        if !matches { continue; }

        let kind = parse_kind(span);

        // For preconditions and laws the primary location is the definition site (file2).
        // For type invariants and everything else it is the VC location (file).
        let location = match &kind {
            GoalKind::Precondition { .. } | GoalKind::Law { .. } => {
                if let Some(loc2) = span.location2() {
                    loc2
                } else if let Some(loc) = span.location() {
                    loc
                } else {
                    continue;
                }
            }
            _ => {
                if let Some(loc) = span.location() {
                    loc
                } else if span.has_coma_ref() {
                    match resolve_cross_ref(cr, span, coma_cache) {
                        Some(loc) => loc,
                        None      => continue,
                    }
                } else {
                    continue;
                }
            }
        };

        // For refinements: primary location is the implementation (coma header),
        // secondary is the trait contract location (from the VC goal term).
        let (kind, location) = if let GoalKind::Refinement { .. } = kind {
            let trait_loc = span.location();
            let impl_loc  = coma_header_location(coma_file);
            let primary   = impl_loc.or_else(|| trait_loc.clone()).unwrap_or(location);
            (GoalKind::Refinement { trait_location: trait_loc }, primary)
        } else {
            (kind, location)
        };

        let display_key = format!("{}|{}|{}|{}|{}",
            span.expl, location.file, location.start_line, location.start_col, kind.label());
        if !seen_display.insert(display_key) { continue; }

        goals.push(Ok(Goal {
            function_name: span.function_name().to_string(),
            kind,
            expl: span.expl.clone(),
            location,
        }));
    }
}

pub fn generate_reports(goals: &[Result<Goal, GoalError>]) -> Vec<annotate_snippets::Group<'_>> {
    use annotate_snippets::{AnnotationKind, Group, Level, Snippet};

    fn load_snippet(location: &Location) -> String {
        use std::io::BufRead;

        fn discard_line(reader: &mut impl std::io::BufRead) {
            loop {
                let buf = reader.fill_buf().expect("failed to read source file");
                if let Some(position) = buf.iter().position(|x| *x == b'\n') {
                    reader.consume(position + 1);
                    break;
                } else {
                    let buf_len = buf.len();
                    reader.consume(buf_len);
                }
            }
        }
        let file = std::fs::File::open(&location.file).expect("failed to open the source file");
        let mut reader = std::io::BufReader::new(file);
        for _ in 1..location.start_line {
            discard_line(&mut reader);
        }
        let mut buf = String::new();
        // TODO: adjust end span and return it
        for _ in location.start_line..=location.end_line {
            reader.read_line(&mut buf).expect("failed to read source file");
        }
        buf
    }

    let mut unknown_goal_kinds = 0;
    let mut reports = Vec::new();
    for goal in goals {
        let goal = match goal {
            Ok(goal) => goal,
            Err(error) => {
                reports.push(Group::with_title(Level::ERROR.primary_title(error.to_string())));
                continue;
            }
        };
        let (primary, annotation, definition) = match &goal.kind {
            GoalKind::Assertion => ("cannot prove assertion", "this assertion could not be proven", None),
            GoalKind::Overflow => ("cannot prove absence of overflow", "this operation could not be proven to be overflow-free", None),
            GoalKind::Panic => ("cannot prove absence of panic", "this panic couldn't be proven to not happen", None),
            GoalKind::LoopInvariantEstablish => ("cannot establish invariant", "this invariant could not be proven to hold when entering the loop", None),
            GoalKind::LoopInvariantPreserve => ("cannot preserve invariant", "this invariant could not be proven to be preserved by the loop", None),
            GoalKind::LoopVariant => ("cannot prove loop variant", "this loop variant could not be proven", None),
            GoalKind::Precondition { definition } => {
                let snippet = load_snippet(definition);
                let annotation = AnnotationKind::Context.span(definition.start_col..definition.end_col).label("the precondition was defined here");
                let definition = Snippet::source(snippet).path(&definition.file).line_start(definition.start_line).annotation(annotation);
                ("cannot prove precondition", "a precondition of this function call could not be proven", Some(definition))
            },
            GoalKind::Postcondition => ("cannot prove postcondition", "this postcondition could not be proven", None),
            GoalKind::Law { definition } => {
                let snippet = load_snippet(definition);
                let annotation = AnnotationKind::Context.span(definition.start_col..definition.end_col).label("the law was defined here");
                let definition = Snippet::source(snippet).path(&definition.file).line_start(definition.start_line).annotation(annotation);
                ("cannot prove law", "the law could not be proven here", Some(definition))
            },
            GoalKind::Refinement { trait_location } => {
                let definition = trait_location.as_ref().map(|definition| {
                    let snippet = load_snippet(definition);
                    let annotation = AnnotationKind::Context.span(definition.start_col..definition.end_col).label("the refinement was defined here");
                    Snippet::source(snippet).path(&definition.file).line_start(definition.start_line).annotation(annotation)
                });
                ("cannot prove refinement", "the refinement could not be proven here", definition)
            },
            GoalKind::TypeInvariant { definition } => {
                let definition = definition.as_ref().map(|definition| {
                    let snippet = load_snippet(definition);
                    let annotation = AnnotationKind::Context.span(definition.start_col..definition.end_col).label("the type invariant is defined here");
                    Snippet::source(snippet).path(&definition.file).line_start(definition.start_line).annotation(annotation)
                });
                ("cannot prove type invariant", "the type invariant of the return value could not be proven here", definition)
            },
            GoalKind::Other => {
                unknown_goal_kinds += 1;
                ("could not prove unknown VC", "something about this code could not be proven", None)
            }
        };
        let snippet = load_snippet(&goal.location);
        let mut report = Level::ERROR
            .primary_title(primary)
            .element(
                Snippet::source(snippet)
                    .line_start(goal.location.start_line)
                    .path(&goal.location.file)
                    .annotation(AnnotationKind::Primary.span(goal.location.start_col..goal.location.end_col).label(annotation))
             );
        if let Some(definition) = definition {
            report = report.element(definition);
        }
        reports.push(report);
    }
    if unknown_goal_kinds > 0 {
        let unknown_goal_kind_text = if unknown_goal_kinds == 1 {
            "The file contains a goal of unknown kind, this is a bug in cargo-creusot - please report it."
        } else {
            "The file contains goals of unknown kind, this is a bug in cargo-creusot - please report it."
        };
        reports.push(Group::with_title(Level::ERROR.primary_title(unknown_goal_kind_text)));
    }
    reports
}

pub fn display_reports(reports: &[annotate_snippets::Group]) {
    if !reports.is_empty() {
        let rendered = annotate_snippets::Renderer::styled().render(&reports);
        println!("{}", rendered);
    }
}

ocaml! {
    fn vc_spans_init_env(conf_v: String);
    fn vc_spans_extract(path: String) -> String;
}

pub enum GoalError {
    /// Currently only UTF-8 paths are supported.
    UnsupportedPath(PathBuf),
    Walk(WalkError),
    ReadSessionFile { path: PathBuf, error: std::io::Error },
    ParseXML { path: PathBuf, error: quick_xml::Error },
    InvalidInt(std::num::ParseIntError),
    Stub(String),
    MalformedRecord { num_lines: usize, record: String },
    OCamlRuntime(String),
}

impl fmt::Display for GoalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use GoalError::*;
        match self {
            OCamlRuntime(error) => write!(f, "failed to initialize OCaml runtime: {}", error),
            UnsupportedPath(path) => write!(f, "non-UTF-8 path: {}", path.display()),
            Walk(error) => write!(f, "cannot walk directory {}: {}", error.path.display(), error.error),
            ReadSessionFile { path, error } => write!(f, "couldn't read session file {}: {}", path.display(), error),
            ParseXML { path, error } => write!(f, "failed to parse session file {}: {}", path.display(), error),
            InvalidInt(error) => write!(f, "invalid integer returned from stub: {}", error),
            Stub(error) => fmt::Display::fmt(error, f),
            MalformedRecord { num_lines, record } => write!(f, "malformed record - expected 18 lines, found {}. Record: {}", num_lines, record),
        }
    }
}

pub struct WalkError {
    path: PathBuf,
    error: std::io::Error,
}

pub fn get_unproved_goals(
    conf_file: &str,
    files: Vec<PathBuf>,
    show_all: bool,
    debug: bool,
) -> Vec<Result<Goal, GoalError>> {
    let _guard = match OCamlRuntime::init() {
        Ok(guard) => guard,
        Err(error) => return vec![Err(GoalError::OCamlRuntime(error))],
    };

    let mut coma_cache = ComaCache::new();
    OCamlRuntime::with_domain_lock(|cr| {
        let conf = format!("{conf_file}:").to_boxroot(cr);
        vc_spans_init_env(cr, &conf);

        // Custom implementation to report errors nicely
        fn maybe_walk_dir(path: PathBuf) -> Box<dyn Iterator<Item=Result<PathBuf, WalkError>>> {
            match std::fs::read_dir(&path) {
                Ok(dir) => Box::new(dir.flat_map(move |result| match result {
                    // Checking the type here skips a syscall on most OSes and introduces one on
                    // others. I think it's worth it.
                    Ok(entry) => {
                        let path = entry.path();
                        match entry.file_type() {
                            Ok(file_type) if file_type.is_dir() => maybe_walk_dir(path),
                            // we don't know, so let's try to open it as directory anyway
                            Err(_) => maybe_walk_dir(path),
                            Ok(file_type) if file_type.is_file() && path.extension() == Some("coma".as_ref()) => {
                                Box::new(std::iter::once(Ok(entry.path())))
                            },
                            Ok(_) => Box::new(std::iter::empty()),
                        }
                    },
                    Err(error) => Box::new(std::iter::once(Err(WalkError { path: path.clone(), error }))),
                })),
                Err(error) if error.kind() == std::io::ErrorKind::NotADirectory && path.extension() == Some("coma".as_ref()) => {
                    Box::new(std::iter::once(Ok(path)))
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotADirectory => {
                    Box::new(std::iter::empty())
                },
                Err(error) => {
                    Box::new(std::iter::once(Err(WalkError { path, error })))
                },
            }
        }

        let mut goals = Vec::new();
        for result in files.into_iter().flat_map(maybe_walk_dir) {
            let coma_file = match result {
                Ok(coma_file) => coma_file,
                Err(error) => {
                    goals.push(Err(GoalError::Walk(error)));
                    continue
                },
            };
            let path = match coma_file.into_os_string().into_string() {
                Ok(path) => path,
                Err(error) => {
                    goals.push(Err(GoalError::UnsupportedPath(error.into())));
                    continue;
                },
            };
            let rooted_path = path.to_boxroot(cr);

            let all_spans = match parse_spans(&vc_spans_extract(cr, &rooted_path).get(cr).as_str()) {
                Ok(s)  => s,
                Err(error) => {
                    goals.push(Err(error));
                    continue;
                }
            };

            collect_unproved_goals(
                cr, path.as_ref(), &all_spans, show_all, debug, &mut coma_cache, &mut goals
            );
        }
        goals
    })
}
