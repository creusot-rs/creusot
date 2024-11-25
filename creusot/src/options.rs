use std::{collections::HashMap, path::PathBuf};

#[derive(Debug, Clone)]
pub enum SpanMode {
    Relative(PathBuf),
    Absolute,
    Off,
}

#[derive(Clone)]
pub enum Why3Sub {
    Prove,
    Ide,
    Replay,
}

#[derive(Clone)]
pub struct Why3Command {
    pub path: PathBuf,
    pub config_file: PathBuf,
    pub sub: Why3Sub,
    pub args: String,
}

#[derive(Clone)]
pub struct Options {
    pub extern_paths: HashMap<String, String>,
    pub metadata_path: Option<String>,
    pub export_metadata: bool,
    pub should_output: bool,
    pub output: Output,
    pub monolithic: bool,
    pub prefix: Vec<why3::Ident>,
    pub in_cargo: bool,
    pub span_mode: SpanMode,
    pub simple_triggers: bool,
    pub why3_cmd: Option<Why3Command>,
}

#[derive(Debug, Clone)]
pub enum Output {
    Directory(PathBuf), // One file per Coma module
    File(PathBuf),      // Monolithic output
    Stdout,
    None,
}
