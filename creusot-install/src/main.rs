#![feature(try_blocks)]
use anyhow::{Context as _, anyhow, bail};
use clap::*;
use creusot_setup::{
    self as setup, Binary, CfgPaths, PROVERS,
    config::{Config, ExternalTool, ManagedTool},
    run,
    tools_versions_urls::*,
};
use indoc::writedoc;
use prelude_generator::build_prelude;
use std::{
    ffi::OsStr,
    fs,
    io::Write,
    os::unix::ffi::OsStrExt as _,
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Clone, Copy)]
pub struct ManagedBinary {
    pub bin: setup::Binary,
    url: &'static Url,
    download: fn(&Url, &Path, &Path) -> anyhow::Result<()>,
}

const ALTERGO: ManagedBinary = ManagedBinary {
    bin: setup::ALTERGO,
    url: &URLS.altergo,
    download: download_from_url_with_cache,
};

const Z3: ManagedBinary =
    ManagedBinary { bin: setup::Z3, url: &URLS.z3, download: download_z3_from_url };

const CVC4: ManagedBinary =
    ManagedBinary { bin: setup::CVC4, url: &URLS.cvc4, download: download_from_url_with_cache };

const CVC5: ManagedBinary =
    ManagedBinary { bin: setup::CVC5, url: &URLS.cvc5, download: download_from_url_with_cache };

/// Install Creusot
#[derive(Debug, Parser)]
struct Args {
    /// Maximum number of provers to run in parallel
    #[arg(long, default_value_t = default_provers_parallelism())]
    provers_parallelism: usize,
    /// Look-up <TOOL> from PATH instead of using the built-in version
    #[arg(long, value_name = "TOOL")]
    external: Vec<SetupManagedTool>,
    /// Do not error if <TOOL>'s version does not match the one expected by creusot
    #[arg(long, value_name = "TOOL")]
    no_check_version: Vec<SetupTool>,
    /// Use existing cargo-creusot
    #[arg(long)]
    skip_cargo_creusot: bool,
    /// Use existing creusot-rustc
    #[arg(long)]
    skip_creusot_rustc: bool,
    /// Skip installing Why3 and Why3find
    #[arg(long)]
    skip_why3: bool,
    /// Skip installing provers
    #[arg(long)]
    skip_extra_tools: bool,
    /// Only build the prelude, don't install anything (implies the skip options)
    #[arg(long)]
    only_build_prelude: bool,
}

fn default_provers_parallelism() -> usize {
    match std::thread::available_parallelism() {
        Ok(n) => n.get(),
        Err(_) => 1,
    }
}

#[derive(Debug, ValueEnum, Clone, PartialEq)]
enum SetupManagedTool {
    Why3AndWhy3find, // skips opam setup
    AltErgo,
    Z3,
    CVC4,
    CVC5,
}

#[derive(Debug, ValueEnum, Clone, PartialEq)]
enum SetupTool {
    Why3,
    Why3find,
    AltErgo,
    Z3,
    CVC4,
    CVC5,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    build_prelude()?;
    if args.only_build_prelude {
        return Ok(());
    }
    install(args)
}

fn install(args: Args) -> anyhow::Result<()> {
    let paths = setup::get_config_paths()?;
    if !args.external.contains(&SetupManagedTool::Why3AndWhy3find) && !args.skip_why3 {
        install_why3(&paths)?;
    }
    if !args.skip_cargo_creusot {
        install_cargo_creusot()?;
    }
    if !args.skip_creusot_rustc {
        install_creusot_rustc(&paths)?;
    }
    if !args.skip_extra_tools {
        install_tools(&paths, args)?;
    }
    Ok(())
}

fn install_why3(cfg: &CfgPaths) -> anyhow::Result<()> {
    println!("Installing Why3 and Why3find...");
    let switch_dir = opam_switch(cfg);
    if fs::exists(switch_dir.join("_opam"))? {
        // Upgrade existing switch
        fs::copy(PathBuf::from("creusot-deps.opam"), switch_dir.join("creusot-deps.opam"))?;
        let mut cmd = Command::new("opam");
        cmd.args(["install", "--yes", "--update-invariant", "--switch"])
            .arg(&switch_dir)
            .arg(switch_dir);
        if !cmd.status()?.success() {
            bail!("Failed to upgrade why3 and why3find")
        }
    } else {
        fs::create_dir_all(&switch_dir)?;
        fs::copy(PathBuf::from("creusot-deps.opam"), switch_dir.join("creusot-deps.opam"))?;
        let mut cmd = Command::new("opam");
        cmd.args(["switch", "create", "-y"]).arg(switch_dir);
        if !cmd.status()?.success() {
            bail!("Failed to create opam switch")
        }
    }
    Ok(())
}

/// Pick opam switch location depending on OS.
/// On macOS we use "$HOME/.creusot" instead of the data directory
/// because Opam fails at handling the space in "Application Support".
#[cfg(not(target_os = "macos"))]
fn opam_switch(cfg: &CfgPaths) -> PathBuf {
    cfg.data_dir.clone() // return a PathBuf because the MacOS version must do so.
}

#[cfg(target_os = "macos")]
fn opam_switch(_: &CfgPaths) -> PathBuf {
    directories::BaseDirs::new().expect("could not find home").home_dir().join(".creusot")
}

fn install_cargo_creusot() -> anyhow::Result<()> {
    println!("Installing cargo-creusot...");
    let mut cmd = Command::new("cargo");
    cmd.args(["install", "--path", "cargo-creusot", "--quiet"]);
    if !cmd.status()?.success() {
        bail!("Failed to install cargo-creusot")
    }
    Ok(())
}

fn install_creusot_rustc(cfg: &setup::CfgPaths) -> anyhow::Result<()> {
    println!("Installing creusot-rustc...");
    let toolchain = setup::toolchain_channel();
    let _ = fs::remove_dir_all(cfg.data_dir.join("toolchains"));
    // Usually ~/.local/share/creusot/toolchains/nightly-YYYY-MM-DD/
    let toolchain_dir = &setup::toolchain_dir(&cfg.data_dir, &toolchain);
    let mut cmd = Command::new("cargo");
    cmd.args(["install", "--path", "creusot-rustc", "--quiet", "--root"]).arg(toolchain_dir);
    if !cmd.status()?.success() {
        bail!("Failed to install creusot-rustc")
    }
    Ok(())
}

fn install_tools(paths: &setup::CfgPaths, args: Args) -> anyhow::Result<()> {
    if args.provers_parallelism < 1 {
        bail! {"--provers-parallelism should be at least 1"}
    }

    // helpers to generate the ExternalTool/ManagedTool config sections

    let get_path = |bin: Binary| -> anyhow::Result<PathBuf> {
        let path = bin.detect_path().ok_or(anyhow!(
            "{} not found. Please install {} version {}",
            &bin.display_name,
            &bin.display_name,
            &bin.version
        ))?;
        println!("Found {} at path: {}", &bin.display_name, &path.display());
        Ok(path)
    };
    let get_opam_path = |tool| -> anyhow::Result<PathBuf> {
        let output = Command::new("opam")
            .args(["exec", "--switch"])
            .arg(opam_switch(paths))
            .args(["--", "which", tool])
            .output()?;
        if !output.status.success() {
            bail!("opam failed to find {}", tool)
        }
        Ok(PathBuf::from(OsStr::from_bytes(output.stdout.trim_ascii_end())))
    };
    let external_tool = |path: PathBuf, name: SetupTool| -> anyhow::Result<ExternalTool> {
        Ok(ExternalTool { path, check_version: !args.no_check_version.contains(&name) })
    };
    let managed_tool =
        |bin: Binary, name: SetupTool, mname: SetupManagedTool| -> anyhow::Result<ManagedTool> {
            if args.external.contains(&mname) {
                Ok(ManagedTool::External(ExternalTool {
                    path: get_path(bin)?,
                    check_version: !args.no_check_version.contains(&name),
                }))
            } else {
                Ok(ManagedTool::Builtin { check_version: !args.no_check_version.contains(&name) })
            }
        };

    let (why3_path, why3find_path) = if args.external.contains(&SetupManagedTool::Why3AndWhy3find) {
        (get_path(setup::WHY3)?, get_path(setup::WHY3FIND)?)
    } else {
        (get_opam_path("why3")?, get_opam_path("why3find")?)
    };

    // build the corresponding configuration

    let config = Config {
        provers_parallelism: std::cmp::max(1, args.provers_parallelism),
        why3: external_tool(why3_path, SetupTool::Why3)?,
        why3find: external_tool(why3find_path, SetupTool::Why3find)?,
        altergo: managed_tool(ALTERGO.bin, SetupTool::AltErgo, SetupManagedTool::AltErgo)?,
        z3: managed_tool(Z3.bin, SetupTool::Z3, SetupManagedTool::Z3)?,
        cvc4: managed_tool(CVC4.bin, SetupTool::CVC4, SetupManagedTool::CVC4)?,
        cvc5: managed_tool(CVC5.bin, SetupTool::CVC5, SetupManagedTool::CVC5)?,
    };

    // check for issues (incorrect versions of external binaries).
    // do not attempt checking version of builtin solvers (we haven't installed
    // them yet, and we know they will be of the expected version).

    let issues = setup::diagnostic_config(paths, &config, false);
    for issue in &issues {
        eprintln!("{issue}")
    }
    if issues.iter().any(|issue| issue.error) {
        bail!("Aborting")
    }

    // apply the configuration to disk
    apply_config(paths, &config)
}

fn apply_config(paths: &setup::CfgPaths, cfg: &Config) -> anyhow::Result<()> {
    // Reset solvers directory
    let _ = fs::remove_dir_all(&paths.bin_subdir);

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
        symlink_file(path, paths.bin_subdir.join(bin.bin.binary_name))?;
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

    // install the why3find package `creusot`
    install_prelude(&cfg.why3find.path)?;

    // This depends on the `creusot` prelude being installed (for `--package creusot`)
    generate_why3find_json(&cfg.why3find.path, &paths.why3_config_file, &paths.config_dir)?;
    Ok(())
}

fn install_prelude(why3find: &PathBuf) -> anyhow::Result<()> {
    Command::new(why3find)
        .current_dir("target")
        .args(["install", "--global", "creusot"])
        .status()?;
    Ok(())
}

// download helper

pub fn sha256sum(file: &Path) -> anyhow::Result<String> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    let mut f = fs::File::open(file).context("opening file to hash")?;
    std::io::copy(&mut f, &mut hasher)?;
    Ok(hex::encode(hasher.finalize()))
}

fn download_from_url(url: &Url, dest: &Path) -> anyhow::Result<()> {
    const DOWNLOAD_RETRIES: u32 = 1;
    let mut success = false;
    let mut tries: u32 = 0;
    while !success && tries <= DOWNLOAD_RETRIES {
        if tries > 0 {
            eprintln!("Retrying...")
        };
        run(Command::new("curl").arg(url.url).arg("-fLo").arg(dest))
            .with_context(|| format!("downloading {} to {}", url.url, dest.display()))?;
        let file_hash = sha256sum(dest)?;
        if file_hash == url.sha256 {
            success = true
        } else {
            eprintln!("Download failed (wrong hash)");
            let _ = fs::remove_file(dest);
        }
        tries += 1;
    }
    if !success {
        bail!("Download failed after {DOWNLOAD_RETRIES} retries (wrong hash?)")
    };
    Ok(())
}

// looks up [cache_dir] to try to find a cached download; if not, stores the
// result of the download in [cache_dir] (using the hash as the filename).
fn download_from_url_with_cache(url: &Url, cache_dir: &Path, dest: &Path) -> anyhow::Result<()> {
    let cached_path = cache_dir.join(url.sha256);
    if !(cached_path.is_file() && sha256sum(&cached_path)? == url.sha256) {
        download_from_url(url, &cached_path)?;
    }
    if cached_path != dest {
        fs::copy(cached_path, dest)?;
    }
    Ok(())
}

// Remember [ide] settings if they exist
fn extract_ide_section(dest_file: &Path) -> Option<String> {
    let file = fs::read_to_string(dest_file).ok()?;
    Some(file.split_at(file.find("[ide]")?).1.split_once("\n\n")?.0.to_string())
}

fn generate_why3_conf(
    provers_parallelism: usize,
    why3_path: &Path,
    bin_dir: &Path,
    dest_file: &Path,
) -> anyhow::Result<()> {
    println!("Generating a fresh why3 configuration...");
    let old_settings: Option<_> = extract_ide_section(dest_file);
    {
        use std::io::Write;
        let mut f = fs::File::create(dest_file)?;
        if let Some(item) = old_settings {
            writeln!(&mut f, "{item}\n").unwrap();
        }
        writeln!(&mut f, "[main]")?;
        writeln!(&mut f, "magic = {WHY3_CONFIG_MAGIC_NUMBER}")?;
        writeln!(&mut f, "running_provers_max = {}", provers_parallelism)?;
    }
    let status = Command::new(why3_path)
        .arg("-C")
        .arg(dest_file)
        .args(["config", "detect"])
        .envs([("PATH", bin_dir)])
        .status()
        .context("launching 'why3 config detect' on downloaded solvers")?;
    if !status.success() {
        bail!("failed to generate why3's configuration")
    };
    {
        let mut f = fs::OpenOptions::new().append(true).open(dest_file)?;
        generate_strategy(&mut f)?;
    }

    Ok(())
}

/// Generate a why3find.json file to be copied when setting up new Creusot projects.
fn generate_why3find_json(
    why3find: &Path,
    why3_config: &Path,
    config_dir: &Path,
) -> anyhow::Result<()> {
    println!("Generating why3find.json...");
    let mut provers = String::new();
    for prover in PROVERS.iter() {
        if !provers.is_empty() {
            provers.push_str(",");
        }
        provers.push_str(&format!("+{}", prover.binary_name));
    }
    let mut why3find = Command::new(why3find);
    why3find
        .args([
            "config",
            "--quiet",
            "--why3-warn-off",
            "unused_variable,axiom_abstract",
            "--package",
            "creusot",
            "--prover",
            &provers,
            "--master",
            "--root",
        ])
        .arg(config_dir)
        .env("WHY3CONFIG", why3_config);
    why3find.status().context(format!("{:?} failed", why3find))?;
    Ok(())
}

fn generate_strategy(f: &mut dyn Write) -> anyhow::Result<()> {
    let altergo = format!("Alt-Ergo,{ALTERGO_VERSION}");
    let z3 = format!("Z3,{Z3_VERSION}");
    let cvc5 = format!("CVC5,{CVC5_VERSION}");
    let cvc4 = format!("CVC4,{CVC4_VERSION}");
    writedoc!(
        f,
        r#"

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
    "#,
    )?;

    Ok(())
}

// download a list [ManagedBinary]s

fn download_all(bins: &[ManagedBinary], cache_dir: &Path, dest_dir: &Path) -> anyhow::Result<()> {
    for bin in bins {
        println!("Downloading {} {}...", bin.bin.display_name, bin.bin.version);
        let path = dest_dir.join(bin.bin.binary_name);
        let dl = bin.download;
        dl(bin.url, cache_dir, &path)?;
        set_executable(&path)?;
    }
    Ok(())
}

// Z3 releases come as a .zip archive that includes many things. We are only
// interested in the z3 binary, so we extract it from the archive and throw away
// the rest.

fn download_z3_from_url(url: &Url, cache_dir: &Path, dest: &Path) -> anyhow::Result<()> {
    use zip::read::ZipArchive;
    // just use the zip file stored in the cache
    let zip_path = cache_dir.join(url.sha256);
    download_from_url_with_cache(url, cache_dir, &zip_path)?;
    {
        // extract the z3 binary from the .zip archive
        let zipfile = std::fs::File::open(&zip_path)?;
        let mut archive = ZipArchive::new(zipfile)?;
        // find out the full path of the z3 binary in the archive
        let z3_archive_path = archive
            .file_names()
            .find(|s| s.ends_with("/bin/z3"))
            .map(String::from)
            .ok_or(anyhow!("did not find a bin/z3 binary in the z3 release archive"))?;
        let mut z3zipfile = archive.by_name(&z3_archive_path)?;
        let mut z3file = fs::File::create(dest)?;
        std::io::copy(&mut z3zipfile, &mut z3file)?;
    }
    Ok(())
}

// cross-platform wrappers

fn set_executable(dest: &Path) -> anyhow::Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(dest)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(dest, perms)?;
    }
    Ok(())
}

fn symlink_file<P: AsRef<Path>, Q: AsRef<Path>>(original: P, link: Q) -> std::io::Result<()> {
    let _ = fs::remove_file(&link);
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(original, link)
    }
    #[cfg(windows)]
    {
        std::os::windows::fs::symlink_file(original, link)
    }
}
