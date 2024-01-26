use clap::*;
use serde::{Deserialize, Serialize};
use std::{error::Error, ffi::OsString};

#[derive(Parser, Serialize, Deserialize)]
pub struct CreusotArgs {
    /// Determines how to format the spans in generated code to loading in Why3.
    /// [Relative] is better if the generated code is meant to be checked into VCS.
    /// [Absolute] means the files can easily be moved around your system and still work.
    /// [None] provides the clearest diffs.
    #[clap(long, value_enum, default_value_t=SpanMode::Relative)]
    pub span_mode: SpanMode,
    #[clap(long)]
    /// Only generate proofs for items matching the provided string. The string is treated
    /// as a Rust qualified path.
    pub focus_on: Option<String>,
    #[clap(long)]
    /// Location that Creusot metadata for this crate should be emitted to.
    pub metadata_path: Option<String>,
    /// Tell creusot to disable metadata exports.
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set)]
    pub export_metadata: bool,
    /// Print to stdout.
    #[clap(group = "output", long)]
    pub stdout: bool,
    /// Print to a file.
    #[clap(group = "output", long, env)]
    pub output_file: Option<String>,
    /// Specify locations of metadata for external crates. The format is the same as rustc's `--extern` flag.
    #[clap(long = "creusot-extern", value_parser= parse_key_val::<String, String>, required=false)]
    pub extern_paths: Vec<(String, String)>,
    /// Check the installed why3 version.
    #[clap(long, default_value_t = true, action = clap::ArgAction::Set)]
    pub check_why3: bool,
    /// Use `result` as the trigger of definition and specification axioms of logic/ghost/predicate functions
    #[clap(long, default_value_t = false, action = clap::ArgAction::Set)]
    pub simple_triggers: bool,
    /// Run why3
    #[command(subcommand)]
    pub subcommand: Option<CreusotSubCommand>,
}

#[derive(Subcommand, Serialize, Deserialize)]
pub enum CreusotSubCommand {
    Why3 {
        /// Why3 subcommand to run
        #[clap(value_enum)]
        command: Why3SubCommand,
        /// Extra arguments to pass to why3
        #[clap(default_value_t = String::default())]
        args: String,
        #[clap(last = true)]
        rust_flags: Vec<String>,
    },
}

#[derive(ValueEnum, Serialize, Deserialize, Clone)]
pub enum Why3SubCommand {
    Prove,
    Ide,
    Replay,
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

impl Args {
    fn move_rust_flags(&mut self) {
        let rust_flags = match &mut self.creusot.subcommand {
            None => return,
            Some(CreusotSubCommand::Why3 { rust_flags, .. }) => rust_flags,
        };
        let rust_flags = std::mem::take(rust_flags);
        assert!(self.rust_flags.is_empty());
        self.rust_flags = rust_flags
    }

    pub fn parse_from<I: Into<OsString> + Clone>(it: impl IntoIterator<Item = I>) -> Self {
        let mut res: Self = Parser::parse_from(it);
        res.move_rust_flags();
        res
    }
}

#[derive(clap::ValueEnum, Clone, Deserialize, Serialize)]
pub enum SpanMode {
    Relative,
    Absolute,
    Off,
}

#[test]
fn test() {}
