use clap::*;
use serde::{Deserialize, Serialize};
use std::error::Error;

#[derive(Parser, Serialize, Deserialize)]
pub struct CreusotArgs {
    /// Determines how to format the spans in generated code to loading in Why3.
    /// [Relative] is better if the generated code is meant to be checked into VCS.
    /// [Absolute] means the files can easily be moved around your system and still work.
    /// [None] provides the clearest diffs.
    #[clap(long, value_enum, default_value_t=SpanMode::Relative)]
    span_mode: SpanMode,
    #[clap(long)]
    /// Only generate proofs for items matching the provided string. The string is treated
    /// as a Rust qualified path.
    focus_on: Option<String>,
    #[clap(long)]
    /// Location that Creusot metadata for this crate should be emitted to.
    metadata_path: Option<String>,
    /// Tell creusot to disable metadata exports.
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set)]
    export_metadata: bool,
    /// Print to stdout.
    #[clap(group = "output", long)]
    stdout: bool,
    /// Print to a file.
    #[clap(group = "output", long, env)]
    output_file: Option<String>,
    /// Specify locations of metadata for external crates. The format is the same as rustc's `--extern` flag.
    #[clap(long = "creusot-extern", value_parser= parse_key_val::<String, String>, required=false)]
    extern_paths: Vec<(String, String)>,
    /// Check the installed why3 version.
    #[clap(long, default_value_t = true, action = clap::ArgAction::Set)]
    pub check_why3: bool,
    /// Use `result` as the trigger of definition and specification axioms of logic/ghost/predicate functions
    #[clap(long, default_value_t = false, action = clap::ArgAction::Set)]
    pub simple_triggers: bool,
    /// Run why3 with the following configuration (Should start with "prove" or "ide")
    #[clap(long)]
    why3: Option<String>,
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

#[derive(Parser)]
pub struct Args {
    #[clap(flatten)]
    pub creusot: CreusotArgs,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}

#[derive(clap::ValueEnum, Clone, Deserialize, Serialize)]
pub enum SpanMode {
    Relative,
    Absolute,
    Off,
}
