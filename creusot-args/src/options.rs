use clap::*;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, error::Error, ffi::OsString, path::PathBuf};

#[derive(Debug, Parser, Serialize, Deserialize)]
#[clap(override_usage = "creusot-rustc [RUSTC_OPTIONS] -- [OPTIONS]")]
pub struct CreusotArgs {
    /// Determines how to format the spans in generated code to loading in Why3.
    ///
    /// [Relative] is better if the generated code is meant to be checked into VCS.
    /// [Absolute] means the files can easily be moved around your system and still work.
    /// [None] provides the clearest diffs.
    /// NB: spans pointing to the Rust standard library are thrown away in [Relative] mode,
    /// while they are kept in [Absolute] mode.
    #[clap(long, value_enum, default_value_t=SpanMode_::Absolute, verbatim_doc_comment)]
    pub span_mode: SpanMode_,
    #[clap(long)]
    /// Directory with respect to which (relative) spans should be relative to.
    /// Necessary when using --stdout with relative spans, not needed otherwise.
    pub spans_relative_to: Option<PathBuf>,
    /// Tell creusot to disable metadata exports.
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set)]
    pub export_metadata: bool,
    /// Print to stdout.
    #[clap(group = "output", long)]
    pub stdout: bool,
    /// Print to a file.
    #[clap(group = "output", long, env)]
    pub output_file: Option<PathBuf>,
    #[clap(group = "output", long, env)]
    pub output_dir: Option<PathBuf>,
    /// Disable output.
    #[clap(group = "output", long, default_value_t = false, action = clap::ArgAction::SetTrue)]
    pub check: bool,
    /// Output the generated code in a single file in output_dir.
    #[clap(long, default_value_t = false, action = clap::ArgAction::SetTrue)]
    pub monolithic: bool,
    /// Specify locations of metadata for external crates. The format is the same as rustc's `--extern` flag.
    #[clap(long = "creusot-extern", value_parser= parse_key_val::<String, PathBuf>, required=false)]
    pub extern_paths: Vec<(String, PathBuf)>,
    /// Use `result` as the trigger of definition and specification axioms of logic/ghost functions
    #[clap(long, default_value_t = false, action = clap::ArgAction::Set)]
    pub simple_triggers: bool,
    /// Enable `#[erasure]` checking across crates.
    #[clap(long, num_args = 0..=1, default_value_t = ErasureCheck::Warn, default_missing_value = "error")]
    pub erasure_check: ErasureCheck,
    /// Directory where cross-crate information for `#[erasure]` checks is stored.
    #[clap(long)]
    pub erasure_check_dir: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, ValueEnum, Serialize, Deserialize)]
pub enum ErasureCheck {
    /// Disable `#[erasure]` checks.
    No,
    /// Output `#[erasure]` check failures as warnings.
    Warn,
    /// Output `#[erasure]` check failures as errors.
    Error,
}

impl ErasureCheck {
    pub fn is_no(&self) -> bool {
        match self {
            ErasureCheck::No => true,
            _ => false,
        }
    }

    pub fn is_error(&self) -> bool {
        match self {
            ErasureCheck::Error => true,
            _ => false,
        }
    }
}

impl std::fmt::Display for ErasureCheck {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ErasureCheck::No => write!(f, "no"),
            ErasureCheck::Warn => write!(f, "warn"),
            ErasureCheck::Error => write!(f, "error"),
        }
    }
}

/// Parse a single key-value pair
fn parse_key_val<T, U>(s: &str) -> Result<(T, U), Box<dyn Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: Error + Send + Sync + 'static,
{
    let pos = s.find('=').ok_or_else(|| format!("invalid KEY=value: no `=` found in `{}`", s))?;
    Ok((s[..pos].parse()?, s[pos + 1..].parse()?))
}

impl CreusotArgs {
    pub fn parse_from<I: Into<OsString> + Clone>(it: impl IntoIterator<Item = I>) -> Self {
        Parser::parse_from(it)
    }
}

#[derive(Debug, clap::ValueEnum, Clone, Deserialize, Serialize)]
pub enum SpanMode_ {
    Relative,
    Absolute,
    Off,
}

// TODO: can we merge Options and CreusotArgs?
// Idk how to parse `SpanMode` directly.

#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum SpanMode {
    Relative(PathBuf),
    Absolute,
    Off,
}

#[derive(Clone)]
pub struct Options {
    pub extern_paths: HashMap<String, PathBuf>,
    pub export_metadata: bool,
    pub should_output: bool,
    pub output: Output,
    pub monolithic: bool,
    pub prefix: Vec<String>,
    pub in_cargo: bool,
    pub span_mode: SpanMode,
    pub simple_triggers: bool,
    pub erasure_check: ErasureCheck,
    pub erasure_check_dir: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub enum Output {
    Directory(PathBuf), // One file per Coma module
    File(PathBuf),      // Monolithic output
    Stdout,
    None,
}

impl CreusotArgs {
    pub fn to_options(self) -> Result<Options, String> {
        let extern_paths = self.extern_paths.into_iter().collect();

        let cargo_creusot = std::env::var("CARGO_CREUSOT").is_ok();
        let should_output = !cargo_creusot || std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

        let output = match (self.stdout, self.output_file, self.output_dir, self.check) {
            (true, None, None, false) => Ok(Output::Stdout),
            (false, Some(f), None, false) => Ok(Output::File(f)),
            (false, None, Some(d), false) => Ok(Output::Directory(d)),
            (false, None, None, true) => Ok(Output::None),
            (false, None, None, false) => Ok(Output::Directory(PathBuf::from("."))), // default --output-dir=.
            _ => Err("--stdout, --output-file, --output-dir, and --check are mutually exclusive"), // This should already be enforced by clap
        }?;

        let span_mode = match (&self.span_mode, &output, &self.spans_relative_to) {
            (SpanMode_::Absolute, _, _) => Ok(SpanMode::Absolute),
            (SpanMode_::Off, _, _) => Ok(SpanMode::Off),
            (SpanMode_::Relative, _, Some(p)) => Ok(SpanMode::Relative(p.to_owned())),
            (SpanMode_::Relative, Output::File(p), None) => {
                Ok(SpanMode::Relative(p.parent().unwrap().to_owned()))
            }
            (SpanMode_::Relative, Output::Directory(p), None) => {
                Ok(SpanMode::Relative(p.to_owned()))
            }
            (SpanMode_::Relative, Output::None, None) => Ok(SpanMode::Off),
            (SpanMode_::Relative, Output::Stdout, None) => {
                Err("--spans-relative-to is required when using --stdout and relative spans")
            }
        }?;

        Ok(Options {
            extern_paths,
            export_metadata: self.export_metadata,
            should_output,
            output,
            in_cargo: cargo_creusot,
            span_mode,
            monolithic: self.monolithic,
            prefix: Vec::new(), // to be set in callbacks::ToWhy::set_output_dir
            simple_triggers: self.simple_triggers,
            erasure_check: self.erasure_check,
            erasure_check_dir: self.erasure_check_dir,
        })
    }
}
