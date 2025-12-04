use anyhow::{Context as _, Result};
use directories::ProjectDirs;
use std::{
    env, fs,
    io::Write as _,
    path::{Path, PathBuf},
    process::Command,
};

mod tools;
pub mod tools_versions_urls;
pub use tools::*;

// CAUTION: on MacOS, [config_dir] and [data_dir] are in fact the same directory
pub struct CreusotPaths {
    cache_dir: PathBuf,
    config_dir: PathBuf,
    data_dir: PathBuf,
}

impl CreusotPaths {
    pub fn new(project_dirs: ProjectDirs) -> Self {
        let data_dir = match env::var("CREUSOT_DATA_HOME").map(PathBuf::from) {
            Ok(path) => path,
            Err(_) => project_dirs.data_dir().to_path_buf(),
        };

        Self {
            cache_dir: project_dirs.cache_dir().to_path_buf(),
            config_dir: project_dirs.config_dir().to_path_buf(),
            data_dir,
        }
    }

    pub fn cache_dir(&self) -> &Path {
        &self.cache_dir
    }

    pub fn config_dir(&self) -> &Path {
        &self.config_dir
    }

    pub fn data_dir(&self) -> &Path {
        &self.data_dir
    }

    pub fn bin(&self) -> PathBuf {
        self.data_dir().join("bin")
    }

    pub fn binary(&self, path: impl AsRef<Path>) -> PathBuf {
        self.bin().join(path)
    }

    pub fn why3_conf(&self) -> PathBuf {
        self.config_dir().join("why3.conf")
    }

    pub fn why3find_json(&self) -> PathBuf {
        self.data_dir().join("why3find.json")
    }

    pub fn why3(&self) -> PathBuf {
        self.binary("why3")
    }

    pub fn why3find(&self) -> PathBuf {
        self.binary("why3find")
    }

    pub fn prelude(&self) -> PathBuf {
        self.data_dir().join("_opam/share/why3find/packages/creusot")
    }
}

pub fn creusot_paths() -> CreusotPaths {
    // arguments: qualifier, organization, application
    // unwrap can't fail because Creusot users have a home
    CreusotPaths::new(ProjectDirs::from("", "creusot", "creusot").unwrap())
}

pub fn toolchain_dir(data_dir: &Path, toolchain: &str) -> PathBuf {
    data_dir.join("toolchains").join(toolchain)
}

pub fn toolchain_channel() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain"))
        .expect("Expected `cargo-creusot` to be built with a valid toolchain file");
    toolchain["toolchain"]["channel"].as_str().unwrap().to_string()
}

pub fn generate_why3_conf(paths: &CreusotPaths, parallelism: Option<usize>) -> Result<()> {
    let why3_conf = paths.why3_conf();
    println!("Refreshing {}", why3_conf.display());
    fs::create_dir_all(paths.config_dir())?;
    let saved_settings = generate_why3_stub(paths, parallelism)?;
    let mut why3 = Command::new(paths.why3());
    why3.args(["config", "detect", "-C"])
        .arg(&why3_conf)
        .env("PATH", paths.bin())
        .status()
        .context("'why3 config detect' failed")?;
    if let Some(saved_settings) = saved_settings {
        let mut file = fs::OpenOptions::new().append(true).open(why3_conf)?;
        writeln!(&mut file, "\n{saved_settings}")?;
    }
    Ok(())
}

/// Create stub `why3.conf` to be completed by `why3 config detect`.
/// If there is already a `why3.conf`, extract its `[ide]` section and return it.
///
/// - Set `running_provers_max` (max number of threads)
/// - Create a `[strategy]` (annoyingly, it must contain specific versions of provers used)
fn generate_why3_stub(
    paths: &CreusotPaths,
    parallelism: Option<usize>,
) -> anyhow::Result<Option<String>> {
    let why3_conf = paths.why3_conf();
    let parallelism = parallelism.unwrap_or_else(default_provers_parallelism);
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

fn default_provers_parallelism() -> usize {
    match std::thread::available_parallelism() {
        Ok(n) => n.get(),
        Err(_) => 1,
    }
}
