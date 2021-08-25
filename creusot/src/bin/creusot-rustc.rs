use std::{
  env,
  path::Path,
  process::{exit, Command},
};

use creusot::util::sysroot_path;

fn main() {
  let mut args = env::args().skip(1).collect::<Vec<_>>();

  // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
  // We're invoking the compiler programmatically, so we ignore this
  if args.len() > 0 && Path::new(&args[0]).file_stem() == Some("rustc".as_ref()) {
    args.remove(0);
  }

  let creusot_driver_path = std::env::current_exe()
    .expect("current executable path invalid")
    .with_file_name("creusot-driver");

  let exit_code = Command::new(creusot_driver_path)
    .args(args)
    .args(vec!["--sysroot".into(), sysroot_path()])
    .arg("-Cpanic=abort".to_owned())
    .arg("-Coverflow-checks=off".to_owned())
    .status()
    .expect("creusot-driver failed to execute");

  if !exit_code.success() {
    exit(exit_code.code().unwrap_or(-1));
  }
}
