use clap::*;
use creusot_args::{CREUSOT_RUSTC_ARGS, options::*};
use creusot_setup as setup;
use std::{
    env,
    io::{IsTerminal as _, Write},
    path::{Display, PathBuf},
    process::{Command, exit},
};
use tempdir::TempDir;

mod helpers;
use helpers::*;
mod why3_launcher;
use why3_launcher::*;
mod why3find_wrapper;
use why3find_wrapper::*;
mod new;
use new::*;

fn main() -> Result<()> {
    let cargs = CargoCreusotArgs::parse_from(std::env::args().skip(1));

    match cargs.subcommand {
        None => creusot(None, cargs.options, cargs.creusot_rustc, cargs.cargo_flags),
        Some(Creusot(subcmd)) => {
            creusot(Some(subcmd), cargs.options, cargs.creusot_rustc, cargs.cargo_flags)
        }
        Some(Setup { command: SetupSubCommand::Status }) => setup::status(),
        Some(Config(args)) => why3find_config(args),
        Some(Prove(args)) => {
            creusot(None, cargs.options, cargs.creusot_rustc, cargs.cargo_flags)?;
            why3find_prove(args)
        }
        Some(New(args)) => new(args),
        Some(Init(args)) => init(args),
        Some(Clean(args)) => clean(args),
    }
}

fn creusot(
    subcmd: Option<CreusotSubCommand>,
    options: CommonOptions,
    creusot_rustc: Option<PathBuf>,
    cargo_flags: Vec<String>,
) -> Result<()> {
    let (coma_src, coma_glob) = get_coma(&options);

    // subcommand analysis:
    //   we want to launch Why3 Ide and replay in cargo-creusot not by creusot-rustc.
    //   however we want to keep the current behavior for other commands: prove
    // why3session will be put in or next to `coma_src`
    let (creusot_rustc_subcmd, launch_why3) = match subcmd {
        Some(CreusotSubCommand::Why3 { command: Why3SubCommand::Ide, args, .. }) => {
            (None, Some((Why3Mode::Ide, coma_src, args)))
        }
        Some(CreusotSubCommand::Why3 { command: Why3SubCommand::Replay, args, .. }) => {
            let mut basename = coma_src.clone();
            basename.set_extension(""); // for single-file mode
            (None, Some((Why3Mode::Replay, basename, args)))
        }
        _ => (subcmd, None),
    };

    // Default output_dir to "." if not specified
    let include_dir = Some(options.output_dir.clone().unwrap_or(".".into()));
    let paths = setup::creusot_paths()?;
    let creusot_args = CreusotArgs {
        options,
        why3_path: paths.why3.clone(),
        why3_config_file: paths.why3.clone(),
        subcommand: creusot_rustc_subcmd.clone(),
    };

    invoke_cargo(&creusot_args, creusot_rustc, cargo_flags);
    warn_if_dangling()?;

    if let Some((mode, coma_src, args)) = launch_why3 {
        let mut coma_files = vec![coma_src];
        // Glob coma files after creusot-rustc has generated them
        if let Why3Mode::Ide = mode {
            if let Some(glob) = coma_glob {
                if let Ok(paths) = glob::glob(&glob) {
                    coma_files.extend(paths.filter_map(|p| p.ok()));
                }
            }
        }

        // why3 configuration
        let why3 = Why3Launcher {
            why3_path: paths.why3,
            config_file: paths.why3_config,
            mode,
            include_dir,
            coma_files,
            args,
        };
        let prelude_dir = TempDir::new("creusot_why3_prelude").expect("could not create temp dir");
        let mut command = why3.make(prelude_dir.path())?;
        command.status().expect("could not run why3");
    }

    Ok(())
}

fn invoke_cargo(args: &CreusotArgs, creusot_rustc: Option<PathBuf>, cargo_flags: Vec<String>) {
    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_cmd = match &args.subcommand {
        Some(CreusotSubCommand::Doc { .. }) => "doc",
        _ => {
            if std::env::var_os("CREUSOT_CONTINUE").is_some() {
                "build"
            } else {
                "check"
            }
        }
    };
    let toolchain = setup::toolchain_channel();
    let creusot_rustc_path = match creusot_rustc {
        Some(path) => path,
        None => setup::toolchain_dir(&setup::get_data_dir().unwrap(), &toolchain)
            .join("bin")
            .join("creusot-rustc"),
    };
    // creusot_rustc binary exists
    if !creusot_rustc_path.exists() {
        eprintln!(
            "creusot-rustc not found (expected at {creusot_rustc_path:?}). You should reinstall Creusot."
        );
        exit(1);
    }
    let mut cmd = Command::new(cargo_path);
    cmd.arg(format!("+{toolchain}"))
        .arg(cargo_cmd)
        .args(cargo_flags)
        .args(["-F", "creusot-contracts/nightly"])
        .env("RUSTC", creusot_rustc_path)
        .env("CARGO_CREUSOT", "1");
    // Incremental compilation causes Creusot to not see all of a crate's code
    // (the `mir_borrowck` hook in `creusot/src/callbacks.rs` is not called on all closures).
    cmd.env("CARGO_INCREMENTAL", "0");

    // Prevent `cargo creusot` and `cargo` from invalidating each other's caches.
    if env::var_os("CARGO_TARGET_DIR").is_none() {
        cmd.env("CARGO_TARGET_DIR", "target/creusot");
    }

    // Append flags to any pre-existing ones
    // CARGO_ENCODED_RUSTFLAGS contains options to pass to rustc, separated by '\x1f'.
    // https://doc.rust-lang.org/cargo/reference/environment-variables.html
    let mut cargo_encoded_rustflags = match std::env::var("CARGO_ENCODED_RUSTFLAGS") {
        Ok(flags) => flags + "\x1f",
        Err(_) => String::new(),
    };
    cargo_encoded_rustflags.push_str("--creusot=");
    cargo_encoded_rustflags.push_str(&serde_json::to_string(&args).unwrap());
    cmd.env("CARGO_ENCODED_RUSTFLAGS", cargo_encoded_rustflags);

    if matches!(&args.subcommand, Some(CreusotSubCommand::Doc { .. })) {
        let mut rustdocflags = String::new();
        for &arg in CREUSOT_RUSTC_ARGS {
            rustdocflags.push_str(arg);
            rustdocflags.push(' ');
        }
        rustdocflags.pop();
        cmd.env("RUSTDOCFLAGS", rustdocflags);
    }

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}

#[derive(Debug, Parser)]
pub struct CargoCreusotArgs {
    #[clap(flatten)]
    pub options: CommonOptions,
    /// Path to creusot-rustc (for testing)
    #[clap(long, value_name = "PATH")]
    pub creusot_rustc: Option<PathBuf>,
    /// Subcommand: why3, setup
    #[command(subcommand)]
    pub subcommand: Option<CargoCreusotSubCommand>,
    /// Additional flags to pass to the underlying cargo invocation.
    #[clap(last = true)]
    #[clap(global = true)]
    pub cargo_flags: Vec<String>,
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
    /// Generate prover configuration
    Config(ConfigArgs),
    /// Run prover on translated files
    Prove(ProveArgs),
    /// Create new project in a sub-directory
    New(NewArgs),
    /// Create new project in current directory
    Init(InitArgs),
    /// Clean dangling files in verif/
    Clean(CleanArgs),
}
use CargoCreusotSubCommand::*;

#[derive(Debug, Parser, Clone)]
pub enum SetupSubCommand {
    /// Show the current status of the Creusot installation
    Status,
}

/// Arguments for `cargo creusot clean`.
#[derive(Debug, Parser)]
pub struct CleanArgs {
    /// Remove dangling files without asking for confirmation.
    #[clap(long)]
    force: bool,
    /// Do not remove any files, only print what would be removed.
    #[clap(long, conflicts_with = "force")]
    dry_run: bool,
}

const OUTPUT_PREFIX: &str = "verif";

/// Remove dangling files in `verif/`
fn clean(options: CleanArgs) -> Result<()> {
    let dangling = find_dangling(&PathBuf::from(OUTPUT_PREFIX))?;
    if dangling.is_empty() {
        eprintln!("No dangling files found");
        return Ok(());
    }
    if !options.force {
        // Ask for confirmation
        eprintln!("The following files and directories will be removed:");
        for path in &dangling {
            eprintln!("  {}", path.display());
        }
        if options.dry_run {
            return Ok(());
        }
        eprint!("Do you want to proceed? [y/N] ");
        std::io::stderr().flush()?;
        let mut input = String::new();
        std::io::stdin().read_line(&mut input)?;
        if !input.trim().eq_ignore_ascii_case("y") {
            return Ok(());
        }
    }
    for path in dangling {
        path.remove()?;
    }
    Ok(())
}

/// Print a warning if there are dangling files in `verif/`
fn warn_if_dangling() -> Result<()> {
    let dangling = find_dangling(&PathBuf::from(OUTPUT_PREFIX))?;
    let is_tty = std::io::stdout().is_terminal();
    if !dangling.is_empty() {
        if is_tty {
            eprint!("\x1b[33mWarning\x1b[0m");
        } else {
            eprint!("Warning");
        }
        eprintln!(": found dangling files and directories:");
        for path in dangling {
            eprintln!("  {}", path.display());
        }
        eprintln!("Run 'cargo creusot clean' to remove them");
    }
    Ok(())
}

enum FileOrDirectory {
    File(PathBuf),
    Directory(PathBuf),
}

use FileOrDirectory::*;

impl FileOrDirectory {
    fn display(&self) -> Display<'_> {
        match self {
            File(path) => path.display(),
            Directory(path) => path.display(),
        }
    }

    fn remove(&self) -> std::io::Result<()> {
        match self {
            File(path) => std::fs::remove_file(&path),
            Directory(path) => std::fs::remove_dir_all(&path),
        }
    }
}

/// Find dangling files in directory `dir`: files named `why3session.xml`, `why3shapes.gz`, and `proof.json`
/// that are not associated with a `.coma` file.
fn find_dangling(dir: &PathBuf) -> Result<Vec<FileOrDirectory>> {
    if !dir.is_dir() {
        return Ok(Vec::new());
    }
    match find_dangling_rec(dir)? {
        None => Ok(vec![Directory(dir.clone())]),
        Some(dangling) => Ok(dangling),
    }
}

/// Find dangling files in directory `dir`.
/// Return `None` if the directory `dir` contains only dangling files,
/// otherwise there must be some non-dangling files in `dir`, return `Some` of only the dangling files and subdirectories.
/// Assumes `dir` exists and is a directory.
fn find_dangling_rec(dir: &PathBuf) -> Result<Option<Vec<FileOrDirectory>>> {
    let mut all_dangling = true;
    let mut dangling = Vec::new();
    let mut has_coma = None; // whether the file "{dir}.coma" exists; only check if needed.
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        let path = entry.path();
        if file_type.is_dir() {
            match find_dangling_rec(&path)? {
                Some(more_dangling) => {
                    dangling.extend(more_dangling);
                    all_dangling = false;
                }
                None => dangling.push(Directory(path)),
            }
        } else if file_type.is_file() {
            let file_name = entry.file_name();
            if [
                "proof.json",
                "why3session.xml",
                "why3shapes.gz",
                "why3session.xml.bak",
                "why3shapes.gz.bak",
            ]
            .contains(&file_name.to_str().unwrap())
            {
                if has_coma.is_none() {
                    has_coma = Some(dir.with_extension("coma").exists());
                }
                if has_coma == Some(false) {
                    dangling.push(File(path));
                } else {
                    all_dangling = false;
                }
            } else {
                all_dangling = false;
            }
        } else {
            // Don't touch symlinks (if they exist maybe there's a good reason)
            all_dangling = false;
        }
    }
    if all_dangling { Ok(None) } else { Ok(Some(dangling)) }
}
