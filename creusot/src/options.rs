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
    pub config_file: Option<PathBuf>,
    pub sub: Why3Sub,
    pub args: String,
}

#[derive(Clone)]
pub struct Options {
    pub extern_paths: HashMap<String, String>,
    pub metadata_path: Option<String>,
    pub export_metadata: bool,
    pub should_output: bool,
    pub output_file: OutputFile,
    pub in_cargo: bool,
    pub span_mode: SpanMode,
    pub match_str: Option<String>,
    pub simple_triggers: bool,
    pub why3_cmd: Option<Why3Command>,
}

#[derive(Debug, Clone)]
pub enum OutputFile {
    File(String),
    Stdout,
}
