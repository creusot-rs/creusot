use serde_json::from_str;
use std::collections::HashMap;

pub struct Options {
    pub extern_paths: HashMap<String, String>,
    pub metadata_path: Option<String>,
    pub continue_compilation: bool,
    pub has_contracts: bool,
    pub be_rustc: bool,
    pub export_metadata: bool,
    pub should_output: bool,
    pub output_file: Option<OutputFile>,
    pub bounds_check: bool,
    pub in_cargo: bool,
    pub span_mode: Option<SpanMode>,
}

pub enum SpanMode {
    Relative,
    Absolute,
}

#[derive(Debug)]
pub enum OutputFile {
    File(String),
    Stdout,
}

impl Options {
    pub fn from_args_and_env(args: &[String]) -> Self {
        // Check if the crate we are compiling has a dependency on contracts, or if it is the contract crate itself.
        // We use this to disable creusot for dependencies if they don't depend on contracts (since that means they will have no real specification)
        let has_contracts =
            args.iter().any(|arg| arg == "creusot_contracts" || arg.contains("creusot_contracts="));

        let be_rustc = args.iter().any(|arg| arg.contains("--print"));

        let cargo_creusot = std::env::var("CARGO_CREUSOT").is_ok();
        // If we're compiling an upstream dependency or we're compiling `creusot_contracts_proc` lets be silent.
        let export_metadata = export_metadata() && cargo_creusot;

        // Either we're not running under `cargo-creusot` (aka `creusot-rustc`) or we are but we're compiling a 'primary' package
        let should_output = !cargo_creusot || std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

        // All options shoudl be parsed before we get here.
        let stdout: bool = args.iter().position(|a| a == "--stdout").is_some() || stdout_output();
        let output_file =
            args.iter().position(|a| a == "-o").map(|ix| args[ix + 1].clone()).or_else(output_file);

        let output_file = match (stdout, output_file) {
            (true, Some(_)) => panic!("cannot set --stdout and output file at the same time"),
            (true, None) => Some(OutputFile::Stdout),
            (false, Some(p)) => Some(OutputFile::File(p)),
            (false, None) => None,
        };

        let extern_paths = match creusot_externs() {
            Some(val) => from_str(&val).expect("could not parse CREUSOT_EXTERNS"),
            None => HashMap::new(),
        };

        let bounds_check = !creusot_unbounded();

        Options {
            has_contracts,
            be_rustc,
            export_metadata,
            should_output,
            output_file,
            continue_compilation: continue_compiler(),
            metadata_path: creusot_metadata_path(),
            extern_paths,
            bounds_check,
            in_cargo: cargo_creusot,
            span_mode: Some(SpanMode::Relative),
        }
    }
}

fn stdout_output() -> bool {
    std::env::var_os("CREUSOT_STDOUT_OUTPUT").is_some()
}

fn output_file() -> Option<String> {
    std::env::var_os("CREUSOT_OUTPUT_FILE").map(|m| m.to_string_lossy().to_string())
}

fn creusot_externs() -> Option<String> {
    std::env::var_os("CREUSOT_EXTERNS").map(|m| m.to_string_lossy().to_string())
}
fn continue_compiler() -> bool {
    std::env::var_os("CREUSOT_CONTINUE").is_some()
}

fn creusot_metadata_path() -> Option<String> {
    std::env::var_os("CREUSOT_METADATA_PATH").map(|m| m.to_string_lossy().to_string())
}

fn export_metadata() -> bool {
    std::env::var_os("CREUSOT_EXPORT_METADATA").map(|f| f != "false").unwrap_or(true)
}

fn creusot_unbounded() -> bool {
    std::env::var_os("CREUSOT_UNBOUNDED").is_some()
}
