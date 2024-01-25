use creusot::options::{self, Options, OutputFile};
pub use creusot_args::options::*;

pub trait CreusotArgsExt {
    fn to_options(self) -> Options;
}
impl CreusotArgsExt for CreusotArgs {
    fn to_options(self) -> Options {
        let metadata_path = self.metadata_path;
        let extern_paths = self.extern_paths.into_iter().collect();

        let cargo_creusot = std::env::var("CARGO_CREUSOT").is_ok();
        let should_output = !cargo_creusot || std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

        let output_file = match (self.stdout, self.output_file) {
            (true, _) => Some(OutputFile::Stdout),
            (_, Some(f)) => Some(OutputFile::File(f)),
            _ => None,
        };

        let span_mode = match self.span_mode {
            SpanMode::Relative => options::SpanMode::Relative,
            SpanMode::Absolute => options::SpanMode::Absolute,
            SpanMode::Off => options::SpanMode::Off,
        };

        Options {
            extern_paths,
            metadata_path,
            export_metadata: self.export_metadata,
            should_output,
            output_file,
            in_cargo: cargo_creusot,
            span_mode: span_mode,
            match_str: self.focus_on,
            simple_triggers: self.simple_triggers,
            why3_cmd: self.why3,
        }
    }
}
