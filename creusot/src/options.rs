use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

#[derive(Clone)]
pub enum SpanMode {
    Relative,
    Absolute,
    Off,
}

#[derive(Clone)]
pub struct Options {
    pub extern_paths: HashMap<String, String>,
    pub metadata_path: Option<String>,
    pub export_metadata: bool,
    pub should_output: bool,
    pub output_file: Option<OutputFile>,
    pub in_cargo: bool,
    pub span_mode: SpanMode,
    pub match_str: Option<String>,
    pub simple_triggers: bool,
}

#[derive(Debug, Clone)]
pub enum OutputFile {
    File(String),
    Stdout,
}

impl Options {
    pub fn relative_to_output(&self, p: &Path) -> PathBuf {
        let mut other = std::env::current_dir().unwrap();
        match &self.output_file {
            Some(OutputFile::File(s)) => {
                if Path::new(s).is_relative() {
                    other.push(s);
                }
            }
            _ => {
                other.push("dummy.mlcfg");
            }
        };

        let two = other.components();
        let one = p.components();

        let mut same = 0;
        one.zip(two).take_while(|(l, r)| l == r).for_each(|_| same += 1);
        let output_components = other.components().count();
        let mut buf = PathBuf::new();

        (0..(output_components - same)).for_each(|_| buf.push(".."));
        buf.extend(p.components().skip(same));
        buf
    }
}
