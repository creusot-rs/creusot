use anyhow::{Context as _, Result, anyhow, bail};
use cargo_metadata::{Metadata, Package, TargetKind, semver::Version};
use clap::*;
use creusot_args::{CREUSOT_RUSTC_ARGS, options::CreusotArgs};
use creusot_setup as setup;
use serde::Deserialize;
use std::{
    env,
    io::{IsTerminal as _, Write},
    path::{Display, Path, PathBuf},
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
        None => creusot(cargs),
        Some(Doc) => doc(cargs),
        Some(New(args)) => new(args),
        Some(Init(args)) => init(args),
        Some(Clean(args)) => clean(args),
        Some(Why3(args)) => why3(args),
        Some(Why3Conf(args)) => why3_conf(args),
        Some(Version) => version(),
    }
}

fn creusot(cargs: CargoCreusotCmds) -> Result<()> {
    let coma = matches!(cargs.args.only, None | Some(Stage::Coma));
    let prove = matches!(cargs.args.only, None | Some(Stage::Prove));
    let runner = Runner::new()?;
    let packages = runner.resolve_packages(&cargs.args.package)?;
    if coma {
        runner.compile(Build::Coma, cargs.args, &packages)?;
    }
    warn_if_dangling()?;
    if prove {
        runner.prove(&packages, cargs.prove_args)?;
    }
    Ok(())
}

fn doc(cargs: CargoCreusotCmds) -> Result<()> {
    let runner = Runner::new()?;
    let packages = runner.resolve_packages(&cargs.args.package)?;
    runner.compile(Build::Doc, cargs.args, &packages)
}

struct Runner {
    metadata: Metadata,
}

impl Runner {
    fn new() -> Result<Self> {
        let metadata = cargo_metadata::MetadataCommand::new().exec()?;
        Ok(Self { metadata })
    }

    fn root(&self) -> &Path {
        self.metadata.workspace_root.as_path().as_std_path()
    }

    fn resolve_packages(&self, packages: &[String]) -> Result<Vec<&Package>> {
        if packages.is_empty() {
            creusot_default_members(&self.metadata)
        } else {
            get_packages_by_name(&self.metadata, packages)
        }
    }

    fn compile(&self, build: Build, args: CargoCreusotArgs, packages: &[&Package]) -> Result<()> {
        if !args.no_check_version {
            check_contracts_version(&self.metadata)?;
        }
        let mut creusot_args = args.creusot_args;
        if !creusot_args.erasure_check.is_no() && creusot_args.erasure_check_dir.is_none() {
            creusot_args.erasure_check_dir =
                Some(self.root().to_path_buf().join("_creusot_erasure"));
        }
        invoke_cargo(
            build,
            creusot_args,
            args.creusot_rustc,
            packages,
            args.cargo_flags,
            self.root(),
        )
    }

    fn prove(&self, packages: &[&Package], prove_args: ProveArgs) -> Result<()> {
        let targets = packages
            .into_iter()
            .flat_map(|package| {
                package.targets.iter().flat_map(|target| {
                    target.kind.iter().filter_map(|kind| {
                        let ty = match kind {
                            TargetKind::Lib | TargetKind::RLib => "rlib",
                            TargetKind::Bin => "bin",
                            _ => return None, // Other types are unsupported at the moment
                        };
                        Some(format!("{}_{}", target.name.replace('-', "_"), ty))
                    })
                })
            })
            .collect();
        why3find_prove(prove_args, self.root(), targets)
    }
}

fn invoke_cargo(
    build: Build,
    args: CreusotArgs,
    creusot_rustc: Option<PathBuf>,
    packages: &[&Package],
    cargo_flags: Vec<String>,
    root: &Path,
) -> Result<()> {
    let cargo_cmd = match build {
        Build::Doc => "doc",
        Build::Coma => {
            if std::env::var_os("CREUSOT_CONTINUE").is_some() {
                "build"
            } else {
                "check"
            }
        }
    };
    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let toolchain = setup::toolchain_channel();
    let creusot_rustc_path = match creusot_rustc {
        Some(path) => path,
        None => setup::toolchain_dir(&setup::creusot_paths().data_dir(), &toolchain)
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
        .args(["-F", "creusot-std/creusot creusot-std/nightly"])
        .env("RUSTUP_TOOLCHAIN", toolchain)
        .env("RUSTC", creusot_rustc_path)
        .env("CARGO_CREUSOT", "1");

    for package in packages {
        cmd.args(["-p", &package.id.to_string()]);
    }

    // Incremental compilation causes Creusot to not see all of a crate's code
    // (the `mir_borrowck` hook in `creusot/src/callbacks.rs` is not called on all closures).
    cmd.env("CARGO_INCREMENTAL", "0");

    // Prevent `cargo creusot` and `cargo` from invalidating each other's caches.
    if env::var_os("CARGO_TARGET_DIR").is_none() {
        cmd.env("CARGO_TARGET_DIR", root.join("target/creusot"));
    }
    cmd.env("CREUSOT_ARGS", serde_json::to_string(&args).unwrap());

    if matches!(build, Build::Doc) {
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

    let exit_status = cmd.status().context("could not run cargo")?;
    if !exit_status.success() {
        bail!("Compilation failed")
    }
    Ok(())
}

/// Get default members to build:
/// either `default-members` in `[workspace.metadata.creusot]`,
/// or get the default members from Cargo.
fn creusot_default_members(metadata: &Metadata) -> Result<Vec<&Package>> {
    match get_explicit_default_members(metadata)? {
        None => Ok(metadata.workspace_packages()),
        Some(members) => Ok(members),
    }
}

/// Get `default-members` from `[workspace.metadata.creusot]`
/// Return `Ok(None)` if the field doesn't exist (so we should fallback to the workspace `default-members`)
/// Return `Err` if the field exist but is invalid (wrong format or unknown packages).
fn get_explicit_default_members(metadata: &Metadata) -> Result<Option<Vec<&Package>>> {
    let custom = &metadata.workspace_metadata;
    let Some(creusot) = custom.get("creusot") else { return Ok(None) };
    check_workspace_metadata(creusot);
    let Some(members) = creusot.get("default-members") else { return Ok(None) };
    let members = <Vec<String>>::deserialize(members)?;
    get_packages_by_name(metadata, &members).map(|packages| Some(packages))
}

fn check_workspace_metadata(value: &serde_json::Value) {
    match value {
        serde_json::Value::Object(map) => {
            for (k, _) in map {
                if k != "default-members" {
                    start_warning();
                    eprintln!(
                        ": in [workspace.metadata.creusot], unexpected field {k:?} (expected \"default-members\")"
                    )
                }
            }
        }
        _ => {
            start_warning();
            eprintln!(
                ": in [workspace.metadata.creusot], unexpected value (expected object with key \"default-members\")"
            )
        }
    }
}

fn get_packages_by_name<'a>(metadata: &'a Metadata, names: &[String]) -> Result<Vec<&'a Package>> {
    names
        .into_iter()
        .map(|member| {
            metadata
                .workspace_packages()
                .into_iter()
                .find(|p| p.name == member)
                .ok_or_else(|| anyhow!("Package not found {}", member))
        })
        .collect()
}

#[derive(Debug, Parser)]
pub struct CargoCreusotCmds {
    /// Subcommand: why3, setup
    #[command(subcommand)]
    pub subcommand: Option<CargoCreusotSubCommand>,
    #[clap(flatten)]
    pub args: CargoCreusotArgs,
    #[clap(flatten)]
    pub prove_args: ProveArgs,
}

#[derive(Debug, Parser)]
pub struct CargoCreusotArgs {
    /// Options for creusot-rustc
    #[clap(flatten)]
    pub creusot_args: CreusotArgs,
    /// Allow mismatching creusot-std versions (use at your own risk!)
    #[clap(long)]
    pub no_check_version: bool,
    /// Path to creusot-rustc (for testing and for Nix)
    #[clap(long, value_name = "PATH", env = "CREUSOT_RUSTC")]
    pub creusot_rustc: Option<PathBuf>,
    #[clap(long, short = 'p', value_name = "PACKAGE")]
    pub package: Vec<String>,
    /// Only run one stage
    #[clap(long)]
    pub only: Option<Stage>,
    /// Additional flags to pass to the underlying cargo invocation.
    #[clap(last = true, global = true)]
    pub cargo_flags: Vec<String>,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub enum Stage {
    /// Compile to Coma
    Coma,
    /// Run provers
    Prove,
}

#[derive(Debug, Subcommand)]
pub enum CargoCreusotSubCommand {
    /// Generate the documentation, including specs, logical functions, etc.
    Doc,
    /// Create new project in a sub-directory
    New(NewArgs),
    /// Create new project in current directory
    Init(InitArgs),
    /// Clean dangling files in verif/
    Clean(CleanArgs),
    /// Run Why3
    Why3(Why3Args),
    /// Regenerate `why3.conf`
    Why3Conf(Why3ConfArgs),
    /// Show version information of Creusot and its dependencies
    Version,
}
use CargoCreusotSubCommand::*;

#[derive(Clone, Copy)]
pub enum Build {
    Coma,
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
    if !dangling.is_empty() {
        start_warning();
        eprintln!(": found dangling files and directories:");
        for path in dangling {
            eprintln!("  {}", path.display());
        }
        eprintln!("Run 'cargo creusot clean' to remove them");
    }
    Ok(())
}

fn start_warning() {
    let is_tty = std::io::stdout().is_terminal();
    if is_tty {
        eprint!("\x1b[33mWarning\x1b[0m");
    } else {
        eprint!("Warning");
    }
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

fn check_contracts_version(metadata: &Metadata) -> Result<()> {
    use std::cmp::Ordering;
    // The cargo-creusot version should be the same as the creusot-std version
    let self_version = Version::parse(CREUSOT_STD_VERSION)?;
    let contracts_version = get_contracts_version(metadata)?;
    let err = |msg, fixes| {
        bail!(
            r"{msg}
    creusot-std {contracts_version}
    creusot     {self_version}
{fixes}"
        )
    };
    match self_version.cmp(&contracts_version) {
        Ordering::Less => err(
            "creusot-std is newer than Creusot.",
            "Possible fixes: upgrade Creusot, or run `cargo creusot init`.",
        ),
        Ordering::Greater => err(
            "creusot-std is out of date.",
            "Possible fixes: run `cargo creusot init` or downgrade Creusot.",
        ),
        Ordering::Equal => Ok(()),
    }
}

fn get_contracts_version(metadata: &Metadata) -> Result<&Version> {
    for package in &metadata.packages {
        if package.name == "creusot-std" {
            return Ok(&package.version);
        }
    }
    Err(anyhow::anyhow!("creusot-std not found in dependencies"))
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
    let paths = setup::creusot_paths();
    run_why3(mode, args.coma_file, args.args, &paths)
}

#[derive(Debug, Parser)]
pub struct Why3ConfArgs {
    #[clap(long)]
    provers_parallelism: Option<usize>,
}

fn why3_conf(args: Why3ConfArgs) -> Result<()> {
    setup::generate_why3_conf(&setup::creusot_paths(), args.provers_parallelism)
}

fn version() -> Result<()> {
    println!("cargo-creusot {}", env!("CARGO_PKG_VERSION"));
    println!("Rust toolchain {}", setup::toolchain_channel());
    let paths = setup::creusot_paths();
    let _ = Command::new(paths.why3()).arg("--version").status();
    let _ = Command::new(paths.why3find()).arg("--version").status();
    for tool in setup::PROVERS {
        let version =
            tool.detect_version(&paths.binary(tool.binary_name)).unwrap_or_else(|e| e.to_string());
        let mismatch = if version != tool.version {
            format!(" (recommended {})", tool.version)
        } else {
            "".into()
        };
        println!("{} {}{}", tool.binary_name, version, mismatch);
    }
    Ok(())
}
