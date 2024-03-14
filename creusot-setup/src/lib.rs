use anyhow::{anyhow, bail, Context};
use directories::ProjectDirs;
use std::{
    fmt, fs,
    path::{Path, PathBuf},
};

mod config;
mod tools;
mod tools_versions_urls;
use config::{Error::*, *};
use tools::*;
use tools_versions_urls::*;
use ToolsConfig::*;

// CAUTION: on MacOS, [config_dir] and [data_dir] are in fact the same directory
struct CfgPaths {
    config_dir: PathBuf,
    config_file: PathBuf,
    why3_config_file: PathBuf,
    data_dir: PathBuf,
    bin_subdir: PathBuf,
    cache_dir: PathBuf,
}

fn get_config_paths(custom_config_dir: &Option<PathBuf>) -> anyhow::Result<CfgPaths> {
    // arguments: qualifier, organization, application
    let dirs = ProjectDirs::from("", "creusot", "creusot")
        .context("failed to compute configuration paths")?;
    let config_dir = match custom_config_dir {
        Some(dir) => dir,
        None => dirs.config_dir(),
    };
    Ok(CfgPaths {
        config_dir: PathBuf::from(config_dir),
        config_file: config_dir.join("Config.toml"),
        why3_config_file: config_dir.join("why3.conf"),
        data_dir: PathBuf::from(dirs.data_dir()),
        bin_subdir: dirs.data_dir().join("bin"),
        cache_dir: PathBuf::from(dirs.cache_dir()),
    })
}

// helpers for diagnostics of a creusot installation.
// used by the implementation of the various subcommands.
struct Issue {
    tool: String,
    cur_version: Option<String>,
    expected_version: String,
}

impl fmt::Display for Issue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Issue { tool, cur_version, expected_version } = self;
        write!(
            f,
            "{tool} has version {}, but version {expected_version} is expected",
            cur_version.as_deref().unwrap_or("(not detected)")
        )
    }
}

fn diagnostic_config(config: &Config) -> Vec<Issue> {
    let mut issues: Vec<Issue> = Vec::new();

    // check versions of the external binaries registered in the config (binary
    // --version vs expected version)
    let extbins = match &config.tools {
        Managed { why3_path, altergo_path, .. } => [(WHY3, why3_path), (ALTERGO, altergo_path)],
        External { why3_path, altergo_path, .. } => [(WHY3, why3_path), (ALTERGO, altergo_path)],
    };
    for (bin, path) in extbins {
        if let DetectedVersion::Bad(ver) = detect_binary_version(&bin, &path) {
            issues.push(Issue {
                tool: bin.display_name.to_owned(),
                cur_version: ver,
                expected_version: bin.version.to_owned(),
            })
        }
    }

    // check versions of the managed binaries (version in the config file vs expected version)
    if let Config { tools: Managed { z3, cvc4, cvc5, .. } } = &config {
        for (cur_version, bin) in [(z3, Z3), (cvc4, CVC4), (cvc5, CVC5)] {
            if cur_version != bin.version {
                issues.push(Issue {
                    tool: bin.display_name.to_owned(),
                    cur_version: Some(cur_version.to_owned()),
                    expected_version: bin.version.to_owned(),
                })
            }
        }
    };

    issues
}

fn diagnostic_extbinary(bin: ExtBinary, issues: &mut Vec<Issue>) -> anyhow::Result<PathBuf> {
    let path = detect_binary_path(&bin).ok_or(anyhow!(
        "{} not found. Please install {} version {}",
        &bin.display_name,
        &bin.display_name,
        &bin.version
    ))?;
    println!("Found {} at path: {}", &bin.display_name, &path.display());
    if let DetectedVersion::Bad(ver) = detect_binary_version(&bin, &path) {
        issues.push(Issue {
            tool: bin.display_name.to_owned(),
            cur_version: ver,
            expected_version: bin.version.to_owned(),
        })
    }
    Ok(path)
}

// display the status of the creusot installation to the user
pub fn status(custom_config_dir: &Option<PathBuf>) -> anyhow::Result<()> {
    let paths = get_config_paths(custom_config_dir)?;
    match Config::read_from_file(&paths.config_file) {
        Err(err) => {
            println!("{err}");
            println!(
                "Hint: run 'cargo creusot setup install' to setup Creusot,\n\
                      or run 'cargo creusot setup' for more information."
            );
        }
        Ok(cfg) => {
            println!("Creusot installation found.");
            print!("{}", cfg.tools);
            let issues = diagnostic_config(&cfg);
            if !issues.is_empty() {
                let severity = match cfg.tools {
                    External { .. } => "Warning",
                    Managed { .. } => "Error",
                };
                println!("");
                for issue in &issues {
                    println!("{severity}: {issue}")
                }
                if let Managed { .. } = cfg.tools {
                    println!(
                        "Hint: for tools installed by Creusot, \
                              re-run 'cargo creusot setup install' \n\
                              to upgrade them to the expected version."
                    )
                }
            }
        }
    };
    Ok(())
}

pub struct CreusotFlags {
    pub why3_path: PathBuf,
    pub why3_config: Option<PathBuf>,
}

/// compute the flags to pass to creusot-rustc.
/// fail if the installation is not in an acceptable state, which means we will
/// stop there and do not attempt launching creusot-rustc.
pub fn status_for_creusot(custom_config_dir: &Option<PathBuf>) -> anyhow::Result<CreusotFlags> {
    let paths = get_config_paths(custom_config_dir)?;
    match Config::read_from_file(&paths.config_file) {
        Err(err) => bail!(
            "{err}\n\
                   Please run 'cargo creusot setup' for more information on \
                   how to perform Creusot's initial setup."
        ),
        Ok(cfg) => {
            match cfg.tools {
                External { why3_path, .. } =>
                // in external mode we assume that everything is setup correctly
                {
                    Ok(CreusotFlags { why3_path, why3_config: None })
                }
                Managed { ref why3_path, .. } => {
                    let issues = diagnostic_config(&cfg);
                    if !issues.is_empty() {
                        for issue in &issues {
                            println!("Error: {issue}")
                        }
                        bail!(
                            "Please run 'cargo creusot setup status' \
                               to diagnostic and fix the issue(s)"
                        )
                    }
                    Ok(CreusotFlags {
                        why3_path: why3_path.to_path_buf(),
                        why3_config: Some(paths.why3_config_file),
                    })
                }
            }
        }
    }
}

pub enum InstallMode {
    Managed,
    External { no_resolve_paths: bool },
}

pub fn install(custom_config_dir: &Option<PathBuf>, mode: InstallMode) -> anyhow::Result<()> {
    let paths = get_config_paths(custom_config_dir)?;

    // figure out whether we're installing a new configuration from scratch, or
    // updating an existing configuration
    let previous_config = match (Config::read_from_file(&paths.config_file), &mode) {
        (Err(NotFound), _) => None,
        (Err(Invalid(_) | WrongVersion(_)), _) => {
            println!("Removing invalid or outdated config...");
            None
        }
        (Ok(Config { tools: Managed { .. } }), InstallMode::External { .. }) => {
            println!(
                "Switching to an installation using external tools. \
                 Erasing current installation..."
            );
            None
        }
        (Ok(Config { tools: External { .. } }), InstallMode::Managed) => {
            println!(
                "Switching to an installation using managed tools. \
                 Erasing current installation..."
            );
            None
        }
        (Ok(cfg), _) => {
            println!("Existing configuration found. Updating.");
            Some(cfg)
        }
    };

    // delete then (re)create the directories we need
    if previous_config.is_none() {
        let _ = fs::remove_dir_all(&paths.config_dir);
        let _ = fs::remove_dir_all(&paths.data_dir);
    }
    fs::create_dir_all(&paths.config_dir)?;
    fs::create_dir_all(&paths.data_dir)?;
    fs::create_dir_all(&paths.bin_subdir)?;
    fs::create_dir_all(&paths.cache_dir)?;

    match mode {
        InstallMode::Managed => install_managed(&paths, previous_config)?,
        InstallMode::External { no_resolve_paths } => install_external(&paths, no_resolve_paths)?,
    };
    Ok(println!("Done."))
}

fn install_external(paths: &CfgPaths, no_resolve_paths: bool) -> anyhow::Result<()> {
    // in external mode, upgrades and fresh installs are equivalent: we
    // write the paths of external binaries.
    let mut issues = Vec::new();
    let why3_path = if no_resolve_paths {
        PathBuf::from(WHY3.binary_name)
    } else {
        diagnostic_extbinary(WHY3, &mut issues)?
    };
    let altergo_path = if no_resolve_paths {
        PathBuf::from(ALTERGO.binary_name)
    } else {
        diagnostic_extbinary(ALTERGO, &mut issues)?
    };
    // in external mode, only warn about issues
    for issue in issues {
        println!("Warning: {issue}")
    }
    let config = Config { tools: External { why3_path, altergo_path } };
    config.write_to_file(&paths.config_file)
}

fn install_managed(paths: &CfgPaths, previous_config: Option<Config>) -> anyhow::Result<()> {
    // reread paths to external binaries
    let mut issues = Vec::new();
    let why3_path = diagnostic_extbinary(WHY3, &mut issues)?;
    let altergo_path = diagnostic_extbinary(ALTERGO, &mut issues)?;
    // in managed mode, issues are failures
    if !issues.is_empty() {
        for issue in issues {
            println!("Error: {issue}")
        }
        bail!("Issues with external binaries.")
    }
    if let Some(Config { tools: Managed { z3, cvc4, cvc5, .. } }) = previous_config {
        // we are upgrading an existing configuration
        let to_upgrade: Vec<_> = [(z3, Z3), (cvc4, CVC4), (cvc5, CVC5)]
            .into_iter()
            .filter(|(cur_ver, bin)| cur_ver != bin.version)
            .map(|(_, bin)| bin)
            .collect();
        managed_download_and_generate_config(paths, &why3_path, &altergo_path, &to_upgrade)
    } else {
        // otherwise this is a fresh install
        managed_download_and_generate_config(paths, &why3_path, &altergo_path, &[Z3, CVC4, CVC5])
    }
}

// in managed mode, download required binaries, then (re)generate configuration
// files for why3 and creusot
fn managed_download_and_generate_config(
    paths: &CfgPaths,
    why3_path: &Path,
    altergo_path: &Path,
    bins: &[Binary],
) -> anyhow::Result<()> {
    // download tool binaries
    download_all(bins, &paths.cache_dir, &paths.bin_subdir)?;

    // create a symbolic link for alt-ergo so that it why3 picks it up
    symlink_file(altergo_path, &paths.bin_subdir.join(ALTERGO.binary_name))?;

    // generate the corresponding .why3.conf
    generate_why3_conf(why3_path, &paths.bin_subdir, &paths.why3_config_file)?;

    // write the config file
    let config = Config {
        tools: Managed {
            why3_path: why3_path.to_owned(),
            altergo_path: altergo_path.to_owned(),
            z3: Z3_VERSION.to_owned(),
            cvc4: CVC4_VERSION.to_owned(),
            cvc5: CVC5_VERSION.to_owned(),
        },
    };
    config.write_to_file(&paths.config_file)
}
