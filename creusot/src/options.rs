use clap::*;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, error::Error};

#[derive(Parser, Serialize, Deserialize)]
pub struct CreusotArgs {
    #[clap(long)]
    unbounded: bool,
    #[clap(long, value_enum)]
    span_mode: Option<SpanMode>,
    #[clap(long)]
    focus_on: Option<String>,
    #[clap(long)]
    metadata_path: Option<String>,
    #[clap(long, default_value_t = true)]
    export_metadata: bool,
    #[clap(group = "output", long)]
    stdout: bool,
    #[clap(group = "output", long)]
    output_file: Option<String>,
    #[clap(long = "creusot-extern", value_parser= parse_key_val::<String, String>, required=false)]
    extern_paths: Vec<(String, String)>,
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
}

pub struct Options {
    pub(crate) extern_paths: HashMap<String, String>,
    pub(crate) metadata_path: Option<String>,
    pub(crate) export_metadata: bool,
    pub(crate) should_output: bool,
    pub(crate) output_file: Option<OutputFile>,
    pub(crate) bounds_check: bool,
    pub(crate) in_cargo: bool,
    pub(crate) span_mode: Option<SpanMode>,
    pub(crate) match_str: Option<String>,
}

#[derive(Debug)]
pub enum OutputFile {
    File(String),
    Stdout,
}

impl Options {
    pub fn from_args(args: CreusotArgs) -> Self {
        let metadata_path = args.metadata_path;
        let extern_paths = args.extern_paths.into_iter().collect();

        let cargo_creusot = std::env::var("CARGO_CREUSOT").is_ok();
        let should_output = !cargo_creusot || std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

        let output_file = match (args.stdout, args.output_file) {
            (true, _) => Some(OutputFile::Stdout),
            (_, Some(f)) => Some(OutputFile::File(f)),
            _ => None,
        };

        Options {
            extern_paths,
            metadata_path,
            export_metadata: args.export_metadata,
            should_output,
            output_file,
            bounds_check: !args.unbounded,
            in_cargo: cargo_creusot,
            span_mode: args.span_mode,
            match_str: args.focus_on,
        }
    }
}
