use std::{
    env,
    process::{exit, Command},
};

use clap::clap_app;

fn main() {
    let creusot_rustc_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("creusot-rustc");
    let cargo_path = env::var("CARGO_PATH").unwrap_or("cargo".to_string());

    let matches = clap_app!(app =>
        (version: "0.1")
        (author: "Xavier Denis <xldenis@lri.fr>")
        (@setting TrailingVarArg)
        (@setting AllowLeadingHyphen)
        (@arg PACKAGE: -p --package [PKG] "package to verify")
        (@arg flags: ... "cargo flags")
    )
    .get_matches_from(std::env::args().skip(2));

    let cargo_cmd = if std::env::var_os("CREUSOT_CONTINUE").is_some() { "build" } else { "check" };

    let mut cmd = Command::new(cargo_path);
    cmd.arg(&cargo_cmd)
        .arg("-q")
        .args(std::env::args().skip(2))
        .env("RUSTC_WRAPPER", creusot_rustc_path);

    if let Some(tgt) = matches.value_of("pkg") {
        cmd.env("CREUSOT_TARGET", tgt);
    };

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}
