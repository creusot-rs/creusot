use creusot_args::options::*;
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
    let mlcfg_filename: PathBuf; //  mlcfg output file name container

    let mut cargs = CargoCreusotArgs::parse_from(std::env::args().skip(1));

    // select mlcfg output file name
    if let Some(f) = &cargs.options.output_file {
        mlcfg_filename = f.into();
    } else {
        mlcfg_filename = make_mlcfg_filename(&cargo_md)?;
        cargs.options.output_file = Some(mlcfg_filename.to_string_lossy().into_owned());
    }

    let subcommand = match cargs.subcommand {
        None => Creusot(None),
        Some(CargoCreusotSubCommand::Creusot(cmd)) => Creusot(Some(cmd)),
        Some(CargoCreusotSubCommand::Setup { command }) => Setup(command),
    };

    match subcommand {
        Creusot(subcmd) => {
            // subcommand analysis:
            //   we want to launch Why3 Ide in cargo-creusot not by creusot-rustc.
            //   however we want to keep the current behavior for other commands: prove and replay
            let (creusot_rustc_subcmd, launch_why3) = if let Some(CreusotSubCommand::Why3 {
                command: Why3SubCommand::Ide,
                ..
            }) = subcmd
            {
                (None, true)
            } else {
                (subcmd, false)
            };

            let config_args = setup::status_for_creusot()?;
            let creusot_args = CreusotArgs {
                options: cargs.options,
                why3_path: config_args.why3_path.clone(),
                why3_config_file: config_args.why3_config.clone(),
                subcommand: creusot_rustc_subcmd.clone(),
                rust_flags: cargs.rust_flags,
            };

            invoke_cargo(&creusot_args);

            if launch_why3 {
                // why3 configuration
                let mut b = Why3LauncherBuilder::new();
                b.why3_path(config_args.why3_path);
                b.config_file(config_args.why3_config);
                b.output_file(mlcfg_filename);
                // temporary: for the moment we only launch why3 via cargo-creusot in Ide mode
                b.mode(Why3Mode::Ide);
                if let Some(subcmd) = &creusot_rustc_subcmd {
                    let CreusotSubCommand::Why3 { args, .. } = subcmd;
                    b.args(args.clone());
                }

                let why3 = b.build()?;
                let prelude_dir =
                    TempDir::new("creusot_why3_prelude").expect("could not create temp dir");
                let mut command = why3.make(prelude_dir.path())?;

                command.status().expect("could not run why3");
            }

            Ok(())
        }
        Setup(SetupSubCommand::Status) => setup::status(),
        Setup(SetupSubCommand::Install { external, no_check_version }) => {
            let extflag =
                |name| setup::ExternalFlag { check_version: !no_check_version.contains(&name) };
            let managedflag = |name, mname| setup::ManagedFlag {
                check_version: !no_check_version.contains(&name),
                external: external.contains(&mname),
            };
            let flags = setup::InstallFlags {
                why3: extflag(SetupTool::Why3),
                altergo: extflag(SetupTool::AltErgo),
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
    let cargo_cmd = if std::env::var_os("CREUSOT_CONTINUE").is_some() { "build" } else { "check" };
    let toolchain = toolchain_channel()
        .expect("Expected `cargo-creusot` to be built with a valid toolchain file");
    let mut cmd = Command::new(cargo_path);
    cmd.arg(format!("+{toolchain}"))
        .arg(&cargo_cmd)
        .args(args.rust_flags.clone())
        .env("RUSTC_WRAPPER", creusot_rustc_path)
        .env("CARGO_CREUSOT", "1");

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
