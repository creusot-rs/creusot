use clap::*;
use creusot_args::{options::*, CREUSOT_RUSTC_ARGS};
use creusot_setup as setup;
use std::{
    env,
    path::PathBuf,
    process::{exit, Command},
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
        Some(Setup {
            command:
                SetupSubCommand::Install {
                    provers_parallelism,
                    external,
                    no_check_version,
                    only_creusot_rustc,
                    skip_creusot_rustc,
                },
        }) => {
            let extflag =
                |name| setup::ExternalFlag { check_version: !no_check_version.contains(&name) };
            let managedflag = |name, mname| setup::ManagedFlag {
                check_version: !no_check_version.contains(&name),
                external: external.contains(&mname),
            };
            let flags = setup::InstallFlags {
                provers_parallelism,
                why3: extflag(SetupTool::Why3),
                why3find: extflag(SetupTool::Why3find),
                altergo: managedflag(SetupTool::AltErgo, SetupManagedTool::AltErgo),
                z3: managedflag(SetupTool::Z3, SetupManagedTool::Z3),
                cvc4: managedflag(SetupTool::CVC4, SetupManagedTool::CVC4),
                cvc5: managedflag(SetupTool::CVC5, SetupManagedTool::CVC5),
                only_creusot_rustc,
                skip_creusot_rustc,
            };
            setup::install(flags)
        }
        Some(Config(args)) => why3find_config(args),
        Some(Prove(args)) => {
            creusot(None, cargs.options, cargs.creusot_rustc, cargs.cargo_flags)?;
            why3find_prove(args)
        }
        Some(New(args)) => new(args),
        Some(Init(args)) => init(args),
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
        eprintln!("creusot-rustc not found (expected at {creusot_rustc_path:?})");
        eprintln!("Run 'cargo creusot setup install' in the source directory of Creusot to install creusot-rustc");
        exit(1);
    }
    let mut cmd = Command::new(cargo_path);
    cmd.arg(format!("+{toolchain}"))
        .arg(cargo_cmd)
        .args(cargo_flags)
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
}
use CargoCreusotSubCommand::*;

#[derive(Debug, Parser, Clone)]
pub enum SetupSubCommand {
    /// Show the current status of the Creusot installation
    Status,
    /// Setup Creusot or update an existing installation
    Install {
        /// Maximum number of provers to run in parallel
        #[arg(long, default_value_t = default_provers_parallelism())]
        provers_parallelism: usize,
        /// Look-up <TOOL> from PATH instead of using the built-in version
        #[arg(long, value_name = "TOOL")]
        external: Vec<SetupManagedTool>,
        /// Do not error if <TOOL>'s version does not match the one expected by creusot
        #[arg(long, value_name = "TOOL")]
        no_check_version: Vec<SetupTool>,
        /// Only install creusot-rustc
        #[arg(long)]
        only_creusot_rustc: bool,
        /// Skip installing creusot-rustc
        #[arg(long, conflicts_with = "only_creusot_rustc")]
        skip_creusot_rustc: bool,
    },
}

fn default_provers_parallelism() -> usize {
    match std::thread::available_parallelism() {
        Ok(n) => n.get(),
        Err(_) => 1,
    }
}
