use creusot_args::options::*;
use creusot_setup as setup;
use std::{
    env,
    process::{exit, Command},
};

enum Subcommand {
    // subcommand to pass on to creusot-rustc
    Creusot(Option<CreusotSubCommand>),
    // subcommand to handle in cargo-creusot
    Setup(SetupSubCommand),
}
use Subcommand::*;

fn main() -> anyhow::Result<()> {
    let cargs = CargoCreusotArgs::parse_from(std::env::args().skip(1));

    let subcommand = match cargs.subcommand {
        None => Creusot(None),
        Some(CargoCreusotSubCommand::Creusot(cmd)) => Creusot(Some(cmd)),
        Some(CargoCreusotSubCommand::Setup { command }) => Setup(command),
    };

    match subcommand {
        Creusot(subcmd) => {
            let config_args = setup::status_for_creusot(&cargs.config_dir)?;
            let creusot_args = CreusotArgs {
                options: cargs.options,
                why3_path: config_args.why3_path,
                why3_config_file: config_args.why3_config,
                subcommand: subcmd,
                rust_flags: cargs.rust_flags,
            };
            Ok(invoke_cargo(&creusot_args))
        }
        Setup(SetupSubCommand::Status) => setup::status(&cargs.config_dir),
        Setup(SetupSubCommand::Install) => {
            setup::install(&cargs.config_dir, setup::InstallMode::Managed)
        }
        Setup(SetupSubCommand::InstallExternal { no_resolve_paths }) => {
            setup::install(&cargs.config_dir, setup::InstallMode::External { no_resolve_paths })
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
