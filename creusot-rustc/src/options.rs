use creusot::options::{self, Options, Output};
pub use creusot_args::options::*;
use std::path::PathBuf;

pub trait CreusotArgsExt {
    fn to_options(self) -> Result<Options, String>;
}

fn why3_command(
    path: PathBuf,
    config_file: PathBuf,
    cmd: CreusotSubCommand,
) -> options::Why3Command {
    let CreusotSubCommand::Why3 { command, args, .. } = cmd else {
        unreachable!();
    };
    let sub = match command {
        Why3SubCommand::Prove => options::Why3Sub::Prove,
        Why3SubCommand::Ide => options::Why3Sub::Ide,
        Why3SubCommand::Replay => options::Why3Sub::Replay,
    };
    options::Why3Command { path, config_file, sub, args }
}
impl CreusotArgsExt for CreusotArgs {
    fn to_options(self) -> Result<Options, String> {
        let metadata_path = self.options.metadata_path;
        let extern_paths = self.options.extern_paths.into_iter().collect();

        let cargo_creusot = std::env::var("CARGO_CREUSOT").is_ok();
        let should_output = !cargo_creusot || std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

        let output = match (
            self.options.stdout,
            self.options.output_file,
            self.options.output_dir,
            self.options.check,
        ) {
            (true, None, None, false) => Ok(Output::Stdout),
            (false, Some(f), None, false) => Ok(Output::File(f)),
            (false, None, Some(d), false) => Ok(Output::Directory(d)),
            (false, None, None, true) => Ok(Output::None),
            (false, None, None, false) => Ok(Output::Directory(PathBuf::from("."))), // default --output-dir=.
            _ => Err("--stdout, --output-file, --output-dir, and --check are mutually exclusive"), // This should already be enforced by clap
        }?;

        let span_mode = match (&self.options.span_mode, &output, &self.options.spans_relative_to) {
            (SpanMode::Absolute, _, _) => Ok(options::SpanMode::Absolute),
            (SpanMode::Off, _, _) => Ok(options::SpanMode::Off),
            (SpanMode::Relative, _, Some(p)) => Ok(options::SpanMode::Relative(p.to_owned())),
            (SpanMode::Relative, Output::File(p), None) => {
                Ok(options::SpanMode::Relative(p.parent().unwrap().to_owned()))
            }
            (SpanMode::Relative, Output::Directory(p), None) => {
                Ok(options::SpanMode::Relative(p.to_owned()))
            }
            (SpanMode::Relative, Output::None, None) => Ok(options::SpanMode::Off),
            (SpanMode::Relative, Output::Stdout, None) => {
                Err("--spans-relative-to is required when using --stdout and relative spans")
            }
        }?;

        Ok(Options {
            extern_paths,
            metadata_path,
            export_metadata: self.options.export_metadata,
            should_output,
            output,
            in_cargo: cargo_creusot,
            span_mode,
            monolithic: self.options.monolithic,
            prefix: Vec::new(), // to be set in callbacks::ToWhy::set_output_dir
            simple_triggers: self.options.simple_triggers,
            why3_cmd: match self.subcommand {
                Some(cmd @ CreusotSubCommand::Why3 { .. }) => {
                    Some(why3_command(self.why3_path, self.why3_config_file, cmd))
                }
                _ => None,
            },
        })
    }
}
