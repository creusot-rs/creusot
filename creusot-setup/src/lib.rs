use anyhow::{bail, Context};
use directories::ProjectDirs;
use std::{cmp::Ordering, fmt, path::PathBuf};

pub mod config;
mod tools;
pub mod tools_versions_urls;
use config::*;
pub use tools::*;

// CAUTION: on MacOS, [config_dir] and [data_dir] are in fact the same directory
pub struct CfgPaths {
    pub config_dir: PathBuf,
    pub config_file: PathBuf,
    pub why3_config_file: PathBuf,
    pub data_dir: PathBuf,
    pub bin_subdir: PathBuf,
    pub cache_dir: PathBuf,
}

impl fmt::Display for CfgPaths {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "config: {}", self.config_dir.display())?;
        writeln!(f, "data:   {}", self.data_dir.display())?;
        write!(f, "cache:  {}", self.cache_dir.display())
    }
}

pub fn get_config_paths() -> anyhow::Result<CfgPaths> {
    // arguments: qualifier, organization, application
    let dirs = ProjectDirs::from("", "creusot", "creusot")
        .context("failed to compute configuration paths")?;
    let config_dir = dirs.config_dir();
    Ok(CfgPaths {
        config_dir: PathBuf::from(config_dir),
        config_file: config_dir.join("Config.toml"),
        why3_config_file: config_dir.join("why3.conf"),
        data_dir: PathBuf::from(dirs.data_dir()),
        bin_subdir: dirs.data_dir().join("bin"),
        cache_dir: PathBuf::from(dirs.cache_dir()),
    })
}

pub fn get_data_dir() -> anyhow::Result<PathBuf> {
    get_config_paths().map(|config| config.data_dir)
}

pub fn get_why3_config_file() -> anyhow::Result<PathBuf> {
    get_config_paths().map(|config| config.why3_config_file)
}

// helpers for diagnostics of a creusot installation.
// used by the implementation of the various subcommands.
pub struct Issue {
    pub error: bool,
    tool: String,
    cur_version: anyhow::Result<String>,
    expected_version: String,
    builtin_tool: bool,
}

impl fmt::Display for Issue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Issue { error, tool, cur_version, expected_version, builtin_tool: _ } = self;
        let header = if *error { "Error" } else { "Warning" };
        match cur_version {
            Ok(cur_version) => write!(f,
                "{header}: {tool} has version {cur_version}, expected version is {expected_version}"),
            Err(err) => write!(f, "{header}: {err}"),
        }
    }
}

pub fn diagnostic_config(paths: &CfgPaths, config: &Config, check_builtins: bool) -> Vec<Issue> {
    let mut issues: Vec<Issue> = Vec::new();

    let mut bins = vec![
        (WHY3, config.why3.check_version, config.why3.path.clone(), false),
        (WHY3FIND, config.why3find.check_version, config.why3find.path.clone(), false),
    ];
    for (bin, cfgbin) in
        [(ALTERGO, &config.altergo), (Z3, &config.z3), (CVC4, &config.cvc4), (CVC5, &config.cvc5)]
    {
        match cfgbin {
            ManagedTool::Builtin { check_version } => {
                if check_builtins {
                    bins.push((
                        bin,
                        *check_version,
                        paths.bin_subdir.clone().join(&bin.binary_name),
                        true,
                    ))
                }
            }
            ManagedTool::External(extbin) => {
                bins.push((bin, extbin.check_version, extbin.path.clone(), false))
            }
        }
    }

    // check versions of binaries (passing --version) vs expected version
    for (bin, check_version, path, builtin_tool) in bins {
        match bin.detect_version(&path) {
            Ok(version) if version == bin.version => continue,
            bad_version => issues.push(Issue {
                error: check_version,
                tool: bin.display_name.to_owned(),
                cur_version: bad_version,
                expected_version: bin.version.to_owned(),
                builtin_tool,
            }),
        }
    }

    issues
}

// Best-effort comparison of version strings
fn version_cmp(v1: &str, v2: &str) -> Option<Ordering> {
    let to_parts = |v: &str| {
        let res: Result<Vec<_>, _> = v.split(|c| c == '.').map(|x| x.parse::<u64>()).collect();
        res
    };
    Some(Vec::cmp(&to_parts(v1).ok()?, &to_parts(v2).ok()?))
}

// display the status of the creusot installation to the user
pub fn status() -> anyhow::Result<()> {
    let paths = get_config_paths()?;
    match Config::read_from_file(&paths.config_file) {
        Err(err) => {
            println!("Creusot installation not found: {err}");
        }
        Ok(cfg) => {
            println!("Creusot installation found.");
            println!("=== INSTALLATION");
            print!("Why3:\n{}", cfg.why3);
            print!("Alt-Ergo:\n{}", cfg.altergo);
            print!("Z3:\n{}", cfg.z3);
            print!("CVC4:\n{}", cfg.cvc4);
            print!("CVC5:\n{}", cfg.cvc5);
            println!("=== PATHS");
            println!("{}", paths);
            let issues = diagnostic_config(&paths, &cfg, true);
            if !issues.is_empty() {
                println!("")
            }
            for issue in &issues {
                println!("{issue}")
            }
            // Try to provide hints for solving the issues
            let needs_upgrade = |issue: &Issue| match &issue.cur_version {
                Err(_) => true,
                Ok(cur_version) => {
                    matches!(
                        version_cmp(&cur_version, &issue.expected_version),
                        Some(Ordering::Less)
                    )
                }
            };
            if issues.iter().any(|issue| issue.builtin_tool && needs_upgrade(&issue)) {
                println!("Hint: reinstall Creusot to upgrade builtin tools.")
            }
            if issues.iter().any(|issue| !issue.builtin_tool && needs_upgrade(&issue)) {
                println!(
                    "Hint: upgrade external tools installed using opam: run 'opam pin . -y' \
                          from your creusot opam switch; you may also need to reinstall Creusot."
                )
            }
            if issues.iter().any(|issue| match &issue.cur_version {
                Err(_) => false,
                Ok(cur_version) => matches!(
                    version_cmp(&cur_version, &issue.expected_version),
                    Some(Ordering::Greater)
                ),
            }) {
                println!("Hint: your creusot binary may be outdated. Please reinstall Creusot.")
            }
        }
    };
    Ok(())
}

pub struct Paths {
    pub why3: PathBuf,
    pub why3find: PathBuf,
    pub why3_config: PathBuf,
}

/// Get paths to tools from Config.toml.
/// fail if the installation is not in an acceptable state
pub fn creusot_paths() -> anyhow::Result<Paths> {
    let paths = get_config_paths()?;
    match Config::read_from_file(&paths.config_file) {
        Err(err) => bail!(
            "{err}\n\
                   Please run 'cargo creusot setup' for more information on \
                   how to perform Creusot's initial setup."
        ),
        Ok(cfg) => {
            let issues = diagnostic_config(&paths, &cfg, true);
            if issues.iter().any(|issue| issue.error) {
                // Avoid being too verbose, and only print issues (even
                // warnings) if there's a hard error. Otherwise we're spamming
                // testsuite logs, etc.
                for issue in &issues {
                    eprintln!("{issue}")
                }
                bail!(
                    "Please run 'cargo creusot setup status' \
                     to diagnostic and fix the issue(s)"
                )
            }
            Ok(Paths {
                why3: cfg.why3.path.to_path_buf(),
                why3find: cfg.why3find.path.to_path_buf(),
                why3_config: paths.why3_config_file,
            })
        }
    }
}

pub fn toolchain_dir(data_dir: &PathBuf, toolchain: &str) -> PathBuf {
    data_dir.join("toolchains").join(toolchain)
}

pub fn toolchain_channel() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain"))
        .expect("Expected `cargo-creusot` to be built with a valid toolchain file");
    toolchain["toolchain"]["channel"].as_str().unwrap().to_string()
}
