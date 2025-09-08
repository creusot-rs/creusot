use anyhow::{Context as _, Result, bail};
use cargo_metadata::semver::Version;
use clap::*;
use creusot_args::{CREUSOT_RUSTC_ARGS, options::CreusotArgs};
use creusot_setup as setup;
use std::{
    env,
    ffi::OsString,
    io::{IsTerminal as _, Write},
    os::unix::ffi::OsStringExt as _,
    path::{Display, PathBuf},
    process::{Command, exit},
};

mod why3_launcher;
use why3_launcher::*;
mod why3find_wrapper;
use why3find_wrapper::*;
mod new;
use new::*;

fn main() -> Result<()> {
    let cargs = CargoCreusotCmds::parse_from(std::env::args().skip(1));

    match cargs.subcommand {
        None => creusot(None, cargs.args, &workspace_root()?),
        Some(Creusot(subcmd)) => creusot(Some(subcmd), cargs.args, &workspace_root()?),
        Some(Setup { command: SetupSubCommand::Status }) => setup::status(),
        Some(Prove(args)) => {
            let root = workspace_root()?;
            creusot(None, cargs.args, &root)?;
            why3find_prove(args, &root)
        }
        Some(New(args)) => new(args),
        Some(Init(args)) => init(args),
        Some(Clean(args)) => clean(args),
        Some(Why3(args)) => why3(args),
    }
}

fn creusot(subcmd: Option<Doc>, args: CargoCreusotArgs, root: &PathBuf) -> Result<()> {
    if !args.no_check_version {
        check_contracts_version()?;
    }
    let mut creusot_args = args.creusot_args;
    if !creusot_args.erasure_check.is_no() && creusot_args.erasure_check_dir.is_none() {
        creusot_args.erasure_check_dir = Some(root.join("_creusot_erasure"));
    }
    invoke_cargo(subcmd, creusot_args, args.creusot_rustc, args.cargo_flags, root);
    warn_if_dangling()?;
    Ok(())
}

fn invoke_cargo(
    doc: Option<Doc>,
    args: CreusotArgs,
    creusot_rustc: Option<PathBuf>,
    cargo_flags: Vec<String>,
    root: &PathBuf,
) {
    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_cmd = match &doc {
        Some(Doc::Doc) => "doc",
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
    cmd.arg(cargo_cmd)
        .args(cargo_flags)
        .args(["-F", "creusot-contracts/creusot creusot-contracts/nightly"])
        .env("RUSTUP_TOOLCHAIN", toolchain)
        .env("RUSTC", creusot_rustc_path)
        .env("CARGO_CREUSOT", "1");
    // Incremental compilation causes Creusot to not see all of a crate's code
    // (the `mir_borrowck` hook in `creusot/src/callbacks.rs` is not called on all closures).
    cmd.env("CARGO_INCREMENTAL", "0");

    // Prevent `cargo creusot` and `cargo` from invalidating each other's caches.
    if env::var_os("CARGO_TARGET_DIR").is_none() {
        cmd.env("CARGO_TARGET_DIR", root.join("target/creusot"));
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

    if matches!(doc, Some(Doc::Doc)) {
        let mut rustdocflags = std::env::var("RUSTDOCFLAGS").unwrap_or_else(|_| String::new());
        for &arg in CREUSOT_RUSTC_ARGS {
            if arg == "-Znext-solver=globally" {
                continue;
            }
            rustdocflags.push(' ');
            rustdocflags.push_str(arg);
        }
        cmd.env("RUSTDOCFLAGS", rustdocflags);
    }

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}

fn workspace_root() -> Result<PathBuf> {
    let mut cargo = Command::new("cargo");
    cargo.args(["locate-project", "--workspace", "--message-format=plain"]);
    let mut path = PathBuf::from(OsString::from_vec(
        cargo.output().context("could not find Cargo.toml")?.stdout,
    ));
    path.pop();
    Ok(path)
}

#[derive(Debug, Parser)]
pub struct CargoCreusotCmds {
    /// Subcommand: why3, setup
    #[command(subcommand)]
    pub subcommand: Option<CargoCreusotSubCommand>,
    #[clap(flatten)]
    pub args: CargoCreusotArgs,
}

#[derive(Debug, Parser)]
pub struct CargoCreusotArgs {
    /// Options for creusot-rustc
    #[clap(flatten)]
    pub creusot_args: CreusotArgs,
    /// Allow mismatching creusot-contracts versions (use at your own risk!)
    #[clap(long)]
    pub no_check_version: bool,
    /// Path to creusot-rustc (for testing)
    #[clap(long, value_name = "PATH")]
    pub creusot_rustc: Option<PathBuf>,
    /// Additional flags to pass to the underlying cargo invocation.
    #[clap(last = true, global = true)]
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
    Creusot(Doc),
    /// Run prover on translated files
    Prove(ProveArgs),
    /// Create new project in a sub-directory
    New(NewArgs),
    /// Create new project in current directory
    Init(InitArgs),
    /// Clean dangling files in verif/
    Clean(CleanArgs),
    /// Run Why3
    Why3(Why3Args),
}
use CargoCreusotSubCommand::*;

#[derive(Debug, Subcommand)]
pub enum Doc {
    /// Generates the documentation, including specs, logical functions, etc.
    Doc,
}

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

fn check_contracts_version() -> Result<()> {
    use std::cmp::Ordering;
    // The cargo-creusot version should be the same as the creusot-contracts version
    let self_version = Version::parse(CREUSOT_CONTRACTS_VERSION)?;
    let contracts_version = get_contracts_version()?;
    let err = |msg, fixes| {
        bail!(
            r"{msg}
    creusot-contracts {contracts_version}
    creusot           {self_version}
{fixes}"
        )
    };
    match self_version.cmp(&contracts_version) {
        Ordering::Less => err(
            "creusot-contracts is newer than Creusot.",
            "Possible fixes: upgrade Creusot, or run `cargo creusot init`.",
        ),
        Ordering::Greater => err(
            "creusot-contracts is out of date.",
            "Possible fixes: run `cargo creusot init` or downgrade Creusot.",
        ),
        Ordering::Equal => Ok(()),
    }
}

fn get_contracts_version() -> Result<Version> {
    let metadata = cargo_metadata::MetadataCommand::new().exec()?;
    for package in metadata.packages {
        if package.name == "creusot-contracts" {
            return Ok(package.version);
        }
    }
    Err(anyhow::anyhow!("creusot-contracts not found in dependencies"))
}

/// Arguments for `cargo creusot why3`.
#[derive(Debug, Parser)]
pub struct Why3Args {
    /// Why3 subcommand to run
    #[clap(value_enum)]
    command: Why3SubCommand,
    /// Coma file to load
    #[clap(value_name = "COMA_FILE")]
    coma_file: PathBuf,
    /// Extra arguments to pass to why3
    #[clap(default_value_t = String::default())]
    args: String,
}

#[derive(Debug, ValueEnum, Clone)]
pub enum Why3SubCommand {
    Prove,
    Ide,
    Replay,
}

fn why3(args: Why3Args) -> Result<()> {
    let mode = match args.command {
        Why3SubCommand::Prove => bail!("'cargo creusot why3 prove' is deprecated"),
        Why3SubCommand::Ide => Why3Mode::Ide,
        Why3SubCommand::Replay => Why3Mode::Replay,
    };
    let paths = setup::creusot_paths()?;
    run_why3(mode, args.coma_file, args.args, paths)
}
