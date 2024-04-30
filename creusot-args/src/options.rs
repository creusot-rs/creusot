use clap::*;
use serde::{Deserialize, Serialize};
use std::{error::Error, ffi::OsString, path::PathBuf};

#[derive(Debug, Parser, Serialize, Deserialize)]
pub struct CommonOptions {
    /// Determines how to format the spans in generated code to loading in Why3.
    /// [Relative] is better if the generated code is meant to be checked into VCS.
    /// [Absolute] means the files can easily be moved around your system and still work.
    /// [None] provides the clearest diffs.
    #[clap(long, value_enum, default_value_t=SpanMode::Relative)]
    pub span_mode: SpanMode,
    #[clap(long, default_value_os_t = get_default_root_path_relative_from_output())]
    /// Relative path of the root of the Rust project relative to the output files
    /// of Creusot. This is used when producing [Relative] spans, to know the location
    /// of Rust files corresponding to the generated Why3 files.
    pub root_path_relative_from_output: PathBuf,
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
    /// Use `result` as the trigger of definition and specification axioms of logic/ghost/predicate functions
    #[clap(long, default_value_t = false, action = clap::ArgAction::Set)]
    pub simple_triggers: bool,
}

#[derive(Debug, Parser, Serialize, Deserialize)]
pub struct CreusotArgs {
    #[clap(flatten)]
    pub options: CommonOptions,
    /// Path to the Why3 binary
    #[arg(long, default_value_os_t = PathBuf::from("why3"))]
    pub why3_path: PathBuf,
    /// Specify an alternative location for Why3's configuration
    #[arg(long)]
    pub why3_config_file: Option<PathBuf>,
    #[command(subcommand)]
    pub subcommand: Option<CreusotSubCommand>,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}

#[derive(Debug, Subcommand, Serialize, Deserialize, Clone)]
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

#[derive(Debug, Parser)]
pub struct CargoCreusotArgs {
    #[clap(flatten)]
    pub options: CommonOptions,
    /// Custom path for Creusot's config directory (managed by 'cargo creusot setup')
    #[arg(long)]
    pub config_dir: Option<PathBuf>,
    /// Subcommand: why3, setup
    #[command(subcommand)]
    pub subcommand: Option<CargoCreusotSubCommand>,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}

#[derive(Debug, Subcommand)]
pub enum CargoCreusotSubCommand {
    /// Setup and manage Creusot's installation
    #[command(arg_required_else_help(true))]
    Setup {
        #[command(subcommand)]
        command: SetupSubCommand,
    },
    #[command(flatten)]
    Creusot(CreusotSubCommand),
}

#[derive(Debug, ValueEnum, Serialize, Deserialize, Clone)]
pub enum Why3SubCommand {
    Prove,
    Ide,
    Replay,
}

#[derive(Debug, Parser, Clone)]
pub enum SetupSubCommand {
    /// Show the current status of the Creusot installation
    Status,
    /// Setup Creusot or update an existing installation
    Install,
    /// Setup Creusot but use external tools configured manually (not recommended, for experts)
    InstallExternal {
        /// Do not lookup and resolve paths to the external binaries (they will
        /// instead be looked up in PATH at each Creusot invocation)
        #[arg(long, default_value_t = false)]
        no_resolve_paths: bool,
    },
}

/// Default relative path of the root project wrt the output.
/// This corresponds to the default scenario where the user invokes "cargo creusot"
/// which writes its output in target/debug/
fn get_default_root_path_relative_from_output() -> PathBuf {
    ["..", ".."].iter().collect()
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
    fn move_rust_flags(&mut self) {
        let rust_flags = match &mut self.subcommand {
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

impl CargoCreusotArgs {
    fn move_rust_flags(&mut self) {
        let rust_flags = match &mut self.subcommand {
            Some(CargoCreusotSubCommand::Creusot(CreusotSubCommand::Why3 {
                rust_flags, ..
            })) => rust_flags,
            _ => return,
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

#[derive(Debug, clap::ValueEnum, Clone, Deserialize, Serialize)]
pub enum SpanMode {
    Relative,
    Absolute,
    Off,
}

#[test]
fn test() {}
