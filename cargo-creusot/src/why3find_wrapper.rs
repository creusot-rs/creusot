use anyhow::{Result, anyhow};
use clap::*;
use creusot_setup::{Paths, creusot_paths};
use std::{
    ffi::OsStr,
    path::{Component, Path, PathBuf},
    process::Command,
};

use crate::{
    OUTPUT_PREFIX,
    why3_launcher::{self, Why3Mode},
};

#[derive(Debug, Parser)]
pub struct ProveArgs {
    /// Run Why3 IDE after proof search.
    #[clap(flatten)]
    pub ide: ProveIdeWhen,
    /// Replay proofs only, no update.
    #[clap(long)]
    pub replay: bool,
    /// Do not use the Why3find cache.
    #[clap(long)]
    pub no_cache: bool,
    /// Generate Why3 sessions for why3 ide.
    #[clap(long)]
    pub why3session: bool,
    /// Run why3find on files that match one of the patterns.
    /// Examples: `name`, `name::*`, `m/*/f`, or whole paths `verif/a/M_b.coma`.
    #[clap(value_parser = Pattern::parse)]
    pub patterns: Vec<Pattern>,
}

// Although these two options look similar, they are implemented quite differently.
// - `ide_on_fail` just corresponds to `why3find`'s `-i` flag.
// - `ide_always` is implemented in a more ad hoc way here.
#[derive(Clone, Debug, Parser)]
#[group(multiple = false)]
pub struct ProveIdeWhen {
    /// Run why3find and open the IDE on unproved goals only.
    #[clap(long, short = 'i')]
    ide_on_fail: bool,
    /// Run why3find and open the IDE on a single Coma file.
    #[clap(long)]
    ide_always: bool,
}

#[derive(Debug, Parser)]
pub struct ConfigArgs {
    /// All arguments are forwarded to `why3find config`; see `why3find config --help` for a list of options.
    #[clap(allow_hyphen_values = true)]
    pub args: Vec<String>,
}

fn check_why3find_json_exists(root: &PathBuf) -> Result<()> {
    let why3find = root.join("why3find.json");
    if why3find.exists() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "{} not found. Perhaps you are in the wrong directory, or you need to run `cargo creusot init`.",
            why3find.display()
        ))
    }
}

fn raw_prove(args: ProveArgs, paths: &Paths, files: &[PathBuf]) -> Result<()> {
    let mut why3find = Command::new(&paths.why3find);
    why3find.arg("prove");
    if args.ide.ide_on_fail {
        why3find.arg("-i");
    }
    if args.replay {
        why3find.arg("-r");
    }
    if args.no_cache {
        why3find.arg("--no-cache");
    }
    // `--ide-always` requires Why3 session files
    if args.why3session || args.ide.ide_always {
        why3find.arg("-s");
    }
    why3find.args(files);
    if let Some(why3_path) = paths.why3.parent() {
        let mut path = why3_path.to_path_buf().into_os_string();
        path.push(":");
        path.push(std::env::var("PATH").unwrap());
        why3find.env("PATH", path);
    }
    why3find
        .env("WHY3CONFIG", &paths.why3_config)
        .status()
        .map_err(|e| anyhow::Error::new(e).context("'why3find prove' failed to launch"))
        .and_then(
            |status| {
                if status.success() { Ok(()) } else { Err(anyhow!("'why3find prove' failed")) }
            },
        )
}

pub fn why3find_prove(args: ProveArgs, root: &PathBuf) -> Result<()> {
    let paths = creusot_paths()?;
    check_why3find_json_exists(root)?;
    let files = match_patterns(&args.patterns)?;
    if files.is_empty() {
        return Ok(());
    }
    // Validate `--ide-always`: it only works with a single Coma file.
    let coma = if !args.ide.ide_always {
        None
    } else if files.len() == 1 && files[0].extension() == Some(OsStr::new("coma")) {
        Some(files[0].clone())
    } else {
        return Err(anyhow!("The flag --ide-always requires exacly one Coma file argument"));
    };
    // If the proof fails, we still want to run the IDE if `--ide-always` was set.
    let prove_result = raw_prove(args, &paths, &files);
    if let Some(coma) = coma {
        why3_launcher::run_why3(Why3Mode::Ide, coma, String::new(), paths)?;
    }
    prove_result
}

/// A pattern is a list of segments which match individual path components.
/// A pattern matches a path if a subsequence of components matches the segments.
/// A pattern must have at least one segment.
///
/// The last component of a path is expected to be of the form `M_example.coma`,
/// and we strip the `M_` and `.coma` before matching.
///
/// Examples:
///
/// - `"a::b"`, `"a/b"` are parsed as the same pattern `[Seg("a"), Seg("b")]`
/// - `"a::b"` matches the files `"verif/a/b/M_z.coma"` and `"verif/a/M_b.coma"`
/// - a file path like `verif/a/M_b.coma` (where the last segment starts with `M_` and ends with `.coma`)
///   can also be used as a pattern which must match a file name exactly (`match_whole` is set to `true`).
#[derive(Clone, Debug)]
pub struct Pattern {
    segments: Vec<Segment>,
    match_whole: bool,
}

impl Pattern {
    /// Argument parser for clap
    fn parse(s: &str) -> Result<Self, Box<dyn std::error::Error + Send + Sync + 'static>> {
        let mut pattern = Pattern {
            segments: s
                .replace("::", "/")
                .split('/')
                .map(|s| if s == "*" { Segment::Any } else { Segment::Seg(s.into()) })
                .collect(),
            match_whole: false,
        };
        let Some(last) = pattern.segments.last_mut() else {
            return Err(anyhow!("Pattern must have at least one segment").into());
        };
        // If the last segment is `M_f.coma` we want to match whole paths against this pattern.
        if let Segment::Seg(last) = last {
            if let Some(stripped) = strip_coma_str(last) {
                *last = stripped.into();
                pattern.match_whole = true;
            }
        }
        Ok(pattern)
    }
}

#[derive(Clone, Debug)]
pub enum Segment {
    Any,
    Seg(String),
}

impl Pattern {
    fn matches(&self, path: &Path) -> bool {
        let components: Box<[_]> = path.components().collect();
        if components.len() < self.segments.len() {
            return false;
        }
        if self.match_whole {
            self.segments.len() == components.len()
                && self.segments.iter().zip(components).all(|(seg, c)| seg.matches(c))
        } else {
            components.len() >= self.segments.len()
                && (0..=components.len() - self.segments.len()).any(|i| {
                    let suffix = &components[i..];
                    self.segments.iter().zip(suffix).all(|(seg, c)| seg.matches(*c))
                })
        }
    }
}

impl Segment {
    fn matches(&self, c: Component) -> bool {
        match self {
            Segment::Any => true,
            Segment::Seg(seg) => match c {
                Component::Normal(c) => c == OsStr::new(seg),
                _ => false,
            },
        }
    }
}

/// `strip_coma("prefix/M_example.coma") == Some("prefix/example")`
fn strip_coma(path: &Path) -> Option<PathBuf> {
    let name = path.file_name()?.to_str()?;
    let name = strip_coma_str(name)?;
    Some(path.with_file_name(name))
}

/// `strip_coma_str("M_example.coma") == Some("example")`
fn strip_coma_str(name: &str) -> Option<&str> {
    name.strip_prefix("M_")?.strip_suffix(".coma")
}

/// If no patterns, return `"verif/"`.
/// Otherwise, list files under `verif/` that match at least one pattern.
fn match_patterns(patterns: &[Pattern]) -> Result<Vec<PathBuf>> {
    if patterns.is_empty() {
        Ok(vec![OUTPUT_PREFIX.into()])
    } else {
        let mut dest = vec![];
        match_patterns_from(patterns, OUTPUT_PREFIX.into(), &mut dest)?;
        Ok(dest)
    }
}

/// Recurse into `dir` and look for file names whose `strip_coma` value matches `patterns`.
fn match_patterns_from(patterns: &[Pattern], dir: PathBuf, dest: &mut Vec<PathBuf>) -> Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        let path = entry.path();
        if file_type.is_dir() {
            match_patterns_from(patterns, path, dest)?
        } else if file_type.is_file() {
            if let Some(spath) = strip_coma(&path) {
                if patterns.iter().any(|pat| pat.matches(&spath)) {
                    dest.push(path)
                }
            }
        }
    }
    Ok(())
}
