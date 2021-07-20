use assert_cmd::prelude::*;
use std::process::Command;
use std::io::Write;
use termcolor::*;


fn main () {
  let why3_path = std::env::var("WHY3_PATH").unwrap_or_else(|_|"why3".into());
  let mut out = StandardStream::stdout(ColorChoice::Always);

  for file in glob::glob("../creusot/tests/should_succeed/*.stdout").unwrap() {
    let file = file.unwrap();
    write!(&mut out, "Testing {} ... ", file.display()).unwrap();

    let mut command = Command::new(why3_path.clone());
    command.arg("prove");
    command.args(&["-L", "../prelude"]);
    command.arg(file);

    let output = command.ok();
    if output.is_ok() {
      out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).unwrap();
      writeln!(&mut out, "ok").unwrap();
    } else {
      out.set_color(ColorSpec::new().set_fg(Some(Color::Red))).unwrap();
      writeln!(&mut out, "failure").unwrap();
    }
    out.reset().unwrap();

    if !output.is_ok() {
      let output = output.unwrap_err();
      let output = output.as_output().unwrap();
      writeln!(&mut out, "{}", std::str::from_utf8(&output.stderr).unwrap()).unwrap();
    }
  }
}
