use anyhow::{anyhow, bail, Context};
use directories::ProjectDirs;
use std::{fmt, fs, path::PathBuf, process::Command};

mod config;
mod tools;
mod tools_versions_urls;
use config::*;
use tools::*;

pub use tools::PROVERS;

// CAUTION: on MacOS, [config_dir] and [data_dir] are in fact the same directory
struct CfgPaths {
    config_dir: PathBuf,
    config_file: PathBuf,
    why3_config_file: PathBuf,
    data_dir: PathBuf,
    bin_subdir: PathBuf,
    cache_dir: PathBuf,
}

impl fmt::Display for CfgPaths {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "config: {}", self.config_dir.display())?;
        writeln!(f, "data:   {}", self.data_dir.display())?;
        write!(f, "cache:  {}", self.cache_dir.display())
    }
}

fn get_config_paths() -> anyhow::Result<CfgPaths> {
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
struct Issue {
    error: bool,
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

fn diagnostic_config(paths: &CfgPaths, config: &Config, check_builtins: bool) -> Vec<Issue> {
    let mut issues: Vec<Issue> = Vec::new();

    let mut bins = vec![
        (WHY3, config.why3.check_version, config.why3.path.clone(), false),
        (WHY3FIND, config.why3find.check_version, config.why3find.path.clone(), false),
    ];
    for (bin, cfgbin) in [
        (ALTERGO.bin, &config.altergo),
        (Z3.bin, &config.z3),
        (CVC4.bin, &config.cvc4),
        (CVC5.bin, &config.cvc5),
    ] {
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

// display the status of the creusot installation to the user
pub fn status() -> anyhow::Result<()> {
    let paths = get_config_paths()?;
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
            if issues.iter().any(|issue| issue.builtin_tool) {
                println!(
                    "Hint: for tools installed by Creusot, \
                     re-run 'cargo creusot setup install' \n\
                     to upgrade them to the expected version."
                )
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

pub struct ExternalFlag {
    pub check_version: bool,
}

pub struct ManagedFlag {
    pub external: bool,
    pub check_version: bool,
}

pub struct InstallFlags {
    pub provers_parallelism: usize,
    pub why3: ExternalFlag,
    pub why3find: ExternalFlag,
    pub altergo: ManagedFlag,
    pub z3: ManagedFlag,
    pub cvc4: ManagedFlag,
    pub cvc5: ManagedFlag,
    pub only_creusot_rustc: bool,
    pub skip_creusot_rustc: bool,
}

pub fn install(flags: InstallFlags) -> anyhow::Result<()> {
    let paths = get_config_paths()?;
    if !flags.skip_creusot_rustc {
        install_creusot_rustc(&paths)?;
    }
    if !flags.only_creusot_rustc {
        install_tools(&paths, flags)?;
    }
    Ok(())
}

fn install_tools(paths: &CfgPaths, flags: InstallFlags) -> anyhow::Result<()> {
    // helpers to generate the ExternalTool/ManagedTool config sections

    let getpath = |bin: Binary| -> anyhow::Result<PathBuf> {
        let path = bin.detect_path().ok_or(anyhow!(
            "{} not found. Please install {} version {}",
            &bin.display_name,
            &bin.display_name,
            &bin.version
        ))?;
        println!("Found {} at path: {}", &bin.display_name, &path.display());
        Ok(path)
    };

    let external_tool = |bin: Binary, flag: ExternalFlag| -> anyhow::Result<ExternalTool> {
        Ok(ExternalTool { path: getpath(bin)?, check_version: flag.check_version })
    };

    let managed_tool = |bin: Binary, flag: ManagedFlag| -> anyhow::Result<ManagedTool> {
        if flag.external {
            Ok(ManagedTool::External(ExternalTool {
                path: getpath(bin)?,
                check_version: flag.check_version,
            }))
        } else {
            Ok(ManagedTool::Builtin { check_version: flag.check_version })
        }
    };

    // build the corresponding configuration

    let config = Config {
        provers_parallelism: std::cmp::max(1, flags.provers_parallelism),
        why3: external_tool(WHY3, flags.why3)?,
        why3find: external_tool(WHY3FIND, flags.why3find)?,
        altergo: managed_tool(ALTERGO.bin, flags.altergo)?,
        z3: managed_tool(Z3.bin, flags.z3)?,
        cvc4: managed_tool(CVC4.bin, flags.cvc4)?,
        cvc5: managed_tool(CVC5.bin, flags.cvc5)?,
    };

    // check for issues (incorrect versions of external binaries).
    // do not attempt checking version of builtin solvers (we haven't installed
    // them yet, and we know they will be of the expected version).

    let issues = diagnostic_config(&paths, &config, false);
    for issue in &issues {
        eprintln!("{issue}")
    }
    if issues.iter().any(|issue| issue.error) {
        bail!("Aborting")
    }

    // apply the configuration to disk
    apply_config(&paths, &config)
}

fn apply_config(paths: &CfgPaths, cfg: &Config) -> anyhow::Result<()> {
    // erase any previous existing config (but not the cache)
    let _ = fs::remove_dir_all(&paths.config_dir);
    let _ = fs::remove_dir_all(&paths.data_dir.join("bin"));

    // create directories
    fs::create_dir_all(&paths.config_dir)?;
    fs::create_dir_all(&paths.data_dir)?;
    fs::create_dir_all(&paths.bin_subdir)?;
    fs::create_dir_all(&paths.cache_dir)?;

    // separate managed tools into "builtin" (we need to download the binary)
    // and "external" (we have a path to the binary)
    let mut builtin: Vec<ManagedBinary> = Vec::new();
    let mut external: Vec<(ManagedBinary, PathBuf)> = Vec::new();

    for (bin, mode) in
        [(ALTERGO, &cfg.altergo), (Z3, &cfg.z3), (CVC4, &cfg.cvc4), (CVC5, &cfg.cvc5)]
    {
        match mode {
            ManagedTool::Builtin { check_version: _ } => builtin.push(bin),
            ManagedTool::External(tool) => external.push((bin, tool.path.clone())),
        }
    }

    // download binaries for builtins
    download_all(&builtin, &paths.cache_dir, &paths.bin_subdir)?;

    // create symbolic links for external tools so that why3 picks them up
    for (bin, path) in external {
        symlink_file(path, &paths.bin_subdir.join(bin.bin.binary_name))?;
    }

    // generate the corresponding .why3.conf
    generate_why3_conf(
        cfg.provers_parallelism,
        &cfg.why3.path,
        &paths.bin_subdir,
        &paths.why3_config_file,
    )?;

    // write the config file to disk
    cfg.write_to_file(&paths.config_file)?;

    // install the why3find package
    why3find_install(&cfg.why3find.path)?;
    Ok(())
}

fn install_creusot_rustc(cfg: &CfgPaths) -> anyhow::Result<()> {
    println! {"Installing creusot-rustc..."};
    let toolchain = toolchain_channel();
    // The `toolchain` hard-coded in toolchain_channel must match the active toolchain
    let active_toolchain = active_toolchain();
    if !active_toolchain.starts_with(&toolchain) {
        // Ignore the target triple in the full toolchain identifier
        panic!("Active toolchain: {active_toolchain}; expected: {toolchain}; cargo-creusot is probably out of date.");
    }
    let _ = fs::remove_dir_all(&cfg.data_dir.join("toolchains"));
    // Usually ~/.local/share/creusot/toolchains/nightly-YYYY-MM-DD/
    let toolchain_dir =
        &toolchain_dir(&cfg.data_dir, &toolchain).into_os_string().into_string().unwrap();
    let mut cmd = Command::new("cargo");
    cmd.args(["install", "--path", "creusot-rustc", "--root", toolchain_dir, "--quiet"]);
    if !cmd.status()?.success() {
        bail!("Failed to install creusot-rustc")
    }
    Ok(())
}

fn active_toolchain() -> String {
    let output = Command::new("rustup").args(&["show", "active-toolchain"]).output().unwrap();
    let output = String::from_utf8(output.stdout).unwrap();
    let toolchain = output.split(" ").next().unwrap();
    toolchain.to_string()
}

pub fn toolchain_dir(data_dir: &PathBuf, toolchain: &str) -> PathBuf {
    data_dir.join("toolchains").join(toolchain)
}

pub fn toolchain_channel() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain"))
        .expect("Expected `cargo-creusot` to be built with a valid toolchain file");
    toolchain["toolchain"]["channel"].as_str().unwrap().to_string()
}
