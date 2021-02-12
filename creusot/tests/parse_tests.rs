#![feature(custom_test_frameworks)]
#![test_runner(datatest::runner)]
#![feature(command_access)]

use assert_cmd::prelude::*;
use std::env;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use mktemp::Temp;


#[datatest::files("tests/should_succeed", {
  input in r"^(.*).rs",
  output = r"${1}.mlcfg",
})]

fn should_succeed(input: &Path, output: &Path){
    let mut cmd = Command::cargo_bin("creusot").unwrap();
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.pop();
    d.push("target");
    d.push("debug");

    cmd.envs(env::vars());
    cmd.arg(format!("-L{}/", d.display()));
    cmd.arg(format!("{}", input.display()));

    let dir = Temp::new_dir().unwrap();

    cmd.args(&["-o", &format!("{}/{:?}.mlcfg", dir.as_path().to_str().unwrap(), input.file_stem().unwrap())[..]]);
    println!("Running: {:?}", cmd);
    cmd.assert().success();
    assert!(!file_diff::diff(dir.as_path().to_str().unwrap(), output.to_str().unwrap()));
}

#[datatest::files("tests/should_fail", {
  input in r"^(.*).rs",
})]
fn should_fail(input: &Path){
    let mut cmd = Command::cargo_bin("creusot").unwrap();
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.pop();
    d.push("target");
    d.push("debug");

    cmd.envs(env::vars());
    cmd.arg(format!("-L{}/", d.display()));
    cmd.arg(format!("{}", input.display()));

    println!("Running: {:?}", cmd);
    cmd.assert().failure();
}
