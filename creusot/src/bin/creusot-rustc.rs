use std::{
    env,
    path::Path,
    process::{exit, Command},
};

fn main() {
    let mut args = env::args().skip(1).collect::<Vec<_>>();

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we ignore this
    if !args.is_empty() && Path::new(&args[0]).file_stem() == Some("rustc".as_ref()) {
        args.remove(0);
    }

    let creusot_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("creusot-driver");

    let sysroot = sysroot_path();

    let exit_code = Command::new(creusot_driver_path)
        .args(args)
        .args(vec!["--sysroot".into(), sysroot])
        .status()
        .expect("creusot-driver failed to execute");

    if !exit_code.success() {
        exit(exit_code.code().unwrap_or(-1));
    }
}

fn sysroot_path() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../../rust-toolchain")).unwrap();
    let channel = toolchain["toolchain"]["channel"].as_str().unwrap();

    let output = Command::new("rustup")
        .arg("run")
        .arg(channel)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    print!("{}", String::from_utf8(output.stderr).ok().unwrap());

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}
