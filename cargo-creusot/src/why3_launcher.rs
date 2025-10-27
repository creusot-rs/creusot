use anyhow::{Context as _, Result};
use creusot_setup::{ALTERGO, Binary, CVC4, CVC5, CreusotPaths, Z3};
use std::{
    fs,
    io::Write as _,
    path::{Path, PathBuf},
    process::Command,
};

use crate::Why3ConfArgs;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Why3Mode {
    Ide,
    Replay,
}

impl std::fmt::Display for Why3Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Why3Mode::Ide => f.write_str("ide"),
            Why3Mode::Replay => f.write_str("replay"),
        }
    }
}

pub(crate) fn run_why3(
    mode: Why3Mode,
    coma_file: PathBuf,
    args: String,
    paths: &CreusotPaths,
) -> Result<()> {
    check_why3_conf_exists(paths)?;
    let prelude = std::ffi::OsString::from(String::from_utf8(
        Command::new(paths.why3find()).arg("where").output()?.stdout,
    )?);
    let mut why3 = Command::new(paths.why3());
    why3.args([
        "--warn-off=unused_variable",
        "--warn-off=clone_not_abstract",
        "--warn-off=axiom_abstract",
        "--debug=coma_no_trivial",
        "-L",
    ])
    .arg(&prelude)
    .arg(mode.to_string())
    .arg(coma_file)
    .arg("-C")
    .arg(paths.why3_conf());
    if !args.is_empty() {
        why3.args(args.split_ascii_whitespace());
    }
    why3.status().context("could not run why3")?;
    Ok(())
}

pub(crate) fn check_why3_conf_exists(paths: &CreusotPaths) -> Result<()> {
    if older(&paths.why3_conf(), &paths.data_dir()) {
        generate_why3_conf(paths, &Why3ConfArgs::default())?;
    }
    Ok(())
}

pub(crate) fn generate_why3_conf(paths: &CreusotPaths, args: &Why3ConfArgs) -> Result<()> {
    let why3_conf = paths.why3_conf();
    println!("Refreshing {}", why3_conf.display());
    fs::create_dir_all(paths.config_dir())?;
    let saved_settings = generate_why3_stub(paths, &args)?;
    let mut why3 = Command::new(paths.why3());
    why3.args(["config", "detect", "-C"])
        .arg(&why3_conf)
        .env("PATH", &paths.bin())
        .status()
        .context("'why3 config detect' failed")?;
    if let Some(saved_settings) = saved_settings {
        let mut file = fs::OpenOptions::new().append(true).open(why3_conf)?;
        writeln!(&mut file, "\n{saved_settings}")?;
    }
    Ok(())
}

// `true` if `older` does not exist or is older than `newer`.
pub fn older(older: &Path, newer: &Path) -> bool {
    let Ok(older_meta) = fs::metadata(older) else { return true };
    let Ok(newer_meta) = fs::metadata(newer) else { return false };
    let (Ok(older_time), Ok(newer_time)) = (older_meta.modified(), newer_meta.modified()) else {
        return false;
    };
    older_time < newer_time
}

/// Create stub `why3.conf` to be completed by `why3 config detect`.
/// If there is already a `why3.conf`, extract its `[ide]` section and return it.
///
/// - Set `running_provers_max` (max number of threads)
/// - Create a `[strategy]` (annoyingly, it must contain specific versions of provers used)
fn generate_why3_stub(paths: &CreusotPaths, args: &Why3ConfArgs) -> anyhow::Result<Option<String>> {
    let why3_conf = paths.why3_conf();
    let parallelism = args.provers_parallelism;
    let version = |tool: Binary| tool.detect_version(&paths.binary(tool.binary_name));
    let altergo = format!("Alt-Ergo,{}", version(ALTERGO)?);
    let z3 = format!("Z3,{}", version(Z3)?);
    let cvc5 = format!("CVC5,{}", version(CVC5)?);
    let cvc4 = format!("CVC4,{}", version(CVC4)?);
    let old_settings = extract_ide_section(&why3_conf);
    let mut f = fs::File::create(why3_conf)?;
    write!(
        f,
        r#"[main]
magic = 14
running_provers_max = {parallelism}
memlimit = 1000
timelimit = 5.000000

[strategy]
code = "start:
c {z3} .5 1000
t split_vc start
c {altergo} 3. 2000 | {z3} 3. 2000
c {cvc5} 3. 2000 | {cvc4} 3. 2000
t introduce_premises afterintro
afterintro:
t inline_goal afterinline
g trylongertime
afterinline:
t split_all_full start
trylongertime:
c {altergo} 6. 4000 | {cvc5} 6. 4000 | {z3} 6. 4000 | {cvc4} 6. 4000
"
desc = "Automatic@ run@ of@ provers@ and@ most@ useful@ transformations"
name = "Creusot_Auto"
shortcut = "4"
"#
    )?;
    Ok(old_settings)
}

fn extract_ide_section(why3_conf: &Path) -> Option<String> {
    let file = fs::read_to_string(why3_conf).ok()?;
    let ide = file.split_at(file.find("[ide]")?).1;
    Some(ide.split_once("\n\n").map(|s| s.0).unwrap_or(ide.trim_end()).to_string())
}
