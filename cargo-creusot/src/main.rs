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
enum Subcommand {
    // subcommand to pass on to creusot-rustc
    Creusot(Option<CreusotSubCommand>),
    // subcommand to handle in cargo-creusot
    Setup(SetupSubCommand),
}
use Subcommand::*;

fn main() -> Result<()> {
    let cargo_md = make_cargo_metadata()?;
    let coma_src: PathBuf; //  coma output file name container
    let coma_glob: Option<String>; // glob pattern for all coma files under coma_src

    let mut cargs = CargoCreusotArgs::parse_from(std::env::args().skip(1));

    // select coma output file name
    if let Some(f) = &cargs.options.output_file {
        coma_src = f.into();
        coma_glob = None;
    } else if cargs.options.stdout {
        coma_src = PathBuf::new(); // don't care, dummy value
        coma_glob = None;
    } else {
        // default to --output-dir=target/creusot
        let dir = make_coma_target(&cargo_md)?;
        coma_src = dir.clone();
        cargs.options.output_dir = Some(dir);
        coma_glob = coma_src.to_str().map(|s| s.to_string() + "/**/*.coma");
    }

    let subcommand = match cargs.subcommand {
        None => Creusot(None),
        Some(CargoCreusotSubCommand::Creusot(cmd)) => Creusot(Some(cmd)),
        Some(CargoCreusotSubCommand::Setup { command }) => Setup(command),
    };

    match subcommand {
        Creusot(subcmd) => {
            // subcommand analysis:
            //   we want to launch Why3 Ide and replay in cargo-creusot not by creusot-rustc.
            //   however we want to keep the current behavior for other commands: prove
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

            let include_dir = cargs.options.output_dir.clone();
            let config_args = setup::status_for_creusot()?;
            let creusot_args = CreusotArgs {
                options: cargs.options,
                why3_path: config_args.why3_path.clone(),
                why3_config_file: config_args.why3_config.clone(),
                subcommand: creusot_rustc_subcmd.clone(),
                rust_flags: cargs.rust_flags,
            };

            invoke_cargo(&creusot_args);

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
                    why3_path: config_args.why3_path,
                    config_file: config_args.why3_config,
                    mode,
                    include_dir,
                    coma_files,
                    args,
                };
                let prelude_dir =
                    TempDir::new("creusot_why3_prelude").expect("could not create temp dir");
                let mut command = why3.make(prelude_dir.path())?;
                command.status().expect("could not run why3");
            }

            Ok(())
        }
        Setup(SetupSubCommand::Status) => setup::status(),
        Setup(SetupSubCommand::Install { provers_parallelism, external, no_check_version }) => {
            let extflag =
                |name| setup::ExternalFlag { check_version: !no_check_version.contains(&name) };
            let managedflag = |name, mname| setup::ManagedFlag {
                check_version: !no_check_version.contains(&name),
                external: external.contains(&mname),
            };
            let flags = setup::InstallFlags {
                provers_parallelism,
                why3: extflag(SetupTool::Why3),
                altergo: managedflag(SetupTool::AltErgo, SetupManagedTool::AltErgo),
                z3: managedflag(SetupTool::Z3, SetupManagedTool::Z3),
                cvc4: managedflag(SetupTool::CVC4, SetupManagedTool::CVC4),
                cvc5: managedflag(SetupTool::CVC5, SetupManagedTool::CVC5),
            };
            setup::install(flags)
        }
    }
}

fn invoke_cargo(args: &CreusotArgs) {
    let creusot_rustc_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("creusot-rustc");

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
    let toolchain = toolchain_channel()
        .expect("Expected `cargo-creusot` to be built with a valid toolchain file");
    let mut cmd = Command::new(cargo_path);
    cmd.arg(format!("+{toolchain}"))
        .arg(&cargo_cmd)
        .args(args.rust_flags.clone())
        .env("RUSTC_WRAPPER", creusot_rustc_path)
        .env("CARGO_CREUSOT", "1");

    if matches!(&args.subcommand, Some(CreusotSubCommand::Doc { .. })) {
        let mut rustdocflags = String::new();
        for &arg in CREUSOT_RUSTC_ARGS {
            rustdocflags.push_str(arg);
            rustdocflags.push(' ');
        }
        rustdocflags.pop();
        cmd.env("RUSTDOCFLAGS", rustdocflags);
    }

    cmd.env("CREUSOT_ARGS", serde_json::to_string(&args).unwrap());

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}

fn toolchain_channel() -> Option<String> {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain")).ok()?;
    let channel = toolchain["toolchain"]["channel"].as_str()?;
    Some(channel.into())
}
