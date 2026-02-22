#![feature(exit_status_error, try_blocks)]
use anyhow::{Context as _, anyhow, bail};
use clap::*;
use creusot_setup::{self as setup, Binary, CreusotPaths, tools_versions_urls::*};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Clone, Copy)]
pub struct ManagedBinary {
    pub bin: setup::Binary,
    url: &'static Url,
    download: fn(&Url, &Path, &Path, &Args) -> anyhow::Result<()>,
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
    ManagedBinary { bin: setup::CVC5, url: &URLS.cvc5, download: download_cvc5_from_url };

/// Install Creusot
#[derive(Debug, Parser)]
struct Args {
    /// Look-up <TOOL> from PATH instead of using the built-in version
    #[arg(long, value_name = "TOOL")]
    external: Vec<SetupTool>,
    /// Use existing cargo-creusot
    #[arg(long)]
    skip_cargo_creusot: bool,
    /// Use existing creusot-rustc
    #[arg(long)]
    skip_creusot_rustc: bool,
    /// Skip installing Why3 and Why3find (you must already have them in `$XDG_DATA_HOME/creusot/bin`)
    #[arg(long)]
    skip_why3: bool,
    /// Skip installing why3.conf and why3find.json
    #[arg(long)]
    skip_why3_conf: bool,
    /// Skip installing the Creusot prelude (Why3 library)
    #[arg(long, conflicts_with = "only_build_prelude")]
    skip_prelude: bool,
    /// Skip installing provers
    #[arg(long)]
    skip_extra_tools: bool,
    /// Only build the prelude, don't install anything (implies the skip options)
    #[arg(long)]
    only_build_prelude: bool,
    /// Set the number of available threads for Why3
    #[arg(long)]
    provers_parallelism: Option<usize>,
    /// Only print commands that will write anything
    #[arg(long)]
    dry_run: bool,
}

#[derive(Debug, ValueEnum, Clone, Copy, PartialEq)]
enum SetupTool {
    AltErgo,
    Z3,
    CVC4,
    CVC5,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    if !args.skip_prelude {
        build_prelude(&args)?;
    }
    if args.only_build_prelude {
        return Ok(());
    }
    install(&args)
}

impl Args {
    fn comment(&self) {
        if self.dry_run {
            print!("echo ");
        }
    }

    fn run(&self, mut cmd: Command) -> anyhow::Result<()> {
        if self.dry_run {
            println!("{:?}", cmd);
        } else if !cmd.status()?.success() {
            bail!("Failed: {:?}", cmd)
        }
        Ok(())
    }

    fn create_dir_all(&self, path: &Path) -> anyhow::Result<()> {
        if self.dry_run {
            println!("mkdir -p {}", path.display());
        } else {
            fs::create_dir_all(path)?;
        }
        Ok(())
    }

    fn copy(&self, src: &Path, dst: &Path) -> anyhow::Result<()> {
        if self.dry_run {
            println!("cp {} {}", src.display(), dst.display());
        } else {
            // Remove dst first in case it is a (possibly broken) symlink;
            // fs::copy would otherwise follow the symlink and fail.
            let _ = fs::remove_file(dst);
            fs::copy(src, dst)?;
        }
        Ok(())
    }

    fn symlink_file<P: AsRef<Path>, Q: AsRef<Path>>(
        &self,
        original: P,
        link: Q,
    ) -> anyhow::Result<()> {
        if self.dry_run {
            println!("ln -sf {} {}", original.as_ref().display(), link.as_ref().display());
        } else {
            let _ = fs::remove_file(&link);
            #[cfg(unix)]
            {
                std::os::unix::fs::symlink(original, link)?;
            }
            #[cfg(windows)]
            {
                std::os::windows::fs::symlink_file(original, link)?;
            }
        }
        Ok(())
    }

    fn remove_dir_all(&self, path: &Path) -> anyhow::Result<()> {
        if self.dry_run {
            println!("rm -rf {}", path.display());
        } else {
            fs::remove_dir_all(path)?;
        }
        Ok(())
    }
}

fn build_prelude(args: &Args) -> anyhow::Result<()> {
    let mut cargo = Command::new("cargo");
    cargo.args(["run", "--bin", "prelude-generator"]);
    args.run(cargo)
}

fn install(args: &Args) -> anyhow::Result<()> {
    let paths: CreusotPaths = setup::creusot_paths();
    create_dirs(&paths, args)?;
    if !args.skip_why3 {
        install_why3(&paths, args)?;
    }
    if !args.skip_prelude {
        install_prelude(&paths, args)?;
    }
    if !args.skip_cargo_creusot {
        install_cargo_creusot(args)?;
    }
    if !args.skip_creusot_rustc {
        install_creusot_rustc(&paths, args)?;
    }
    if !args.skip_extra_tools {
        install_tools(&paths, &args)?;
    }
    if !args.skip_why3_conf {
        install_config(&paths, &args)?;
    }
    Ok(())
}

fn create_dirs(paths: &CreusotPaths, args: &Args) -> anyhow::Result<()> {
    args.create_dir_all(&paths.config_dir())?;
    args.create_dir_all(&paths.why3find_libs().join("packages/creusot/creusot"))?;
    args.create_dir_all(&paths.bin())?;
    Ok(())
}

fn install_why3(paths: &CreusotPaths, args: &Args) -> anyhow::Result<()> {
    args.comment();
    println!("Installing Why3 and Why3find...");
    let switch_dir = opam_switch(paths);
    let opam_dir = switch_dir.join("_opam");
    if fs::exists(&opam_dir)? {
        // Upgrade existing switch
        args.copy(&PathBuf::from("creusot-deps.opam"), &switch_dir.join("creusot-deps.opam"))?;
        let mut cmd = Command::new("opam");
        cmd.args(["install", "--yes", "--update-invariant", "--switch"])
            .arg(&switch_dir)
            .arg(switch_dir);
        args.run(cmd)?;
    } else {
        args.create_dir_all(&switch_dir)?;
        args.copy(&PathBuf::from("creusot-deps.opam"), &switch_dir.join("creusot-deps.opam"))?;
        let mut cmd = Command::new("opam");
        cmd.args(["switch", "create", "-y"]).arg(switch_dir);
        args.run(cmd)?;
    }
    args.symlink_file(opam_dir.join("bin/why3"), paths.why3())?;
    args.symlink_file(opam_dir.join("bin/why3find"), paths.why3find())?;
    Ok(())
}

/// Pick opam switch location depending on OS.
/// On macOS we use "$HOME/.creusot" instead of the data directory
/// because Opam fails at handling the space in "Application Support".
#[cfg(not(target_os = "macos"))]
fn opam_switch(cfg: &CreusotPaths) -> PathBuf {
    cfg.data_dir().into() // return a PathBuf because the MacOS version must do so.
}

#[cfg(target_os = "macos")]
fn opam_switch(_: &CreusotPaths) -> PathBuf {
    directories::BaseDirs::new().expect("could not find home").home_dir().join(".creusot")
}

fn install_cargo_creusot(args: &Args) -> anyhow::Result<()> {
    args.comment();
    println!("Installing cargo-creusot...");
    let mut cmd = Command::new("cargo");
    cmd.args(["install", "--path", "cargo-creusot", "--quiet"]);
    args.run(cmd)
}

fn install_creusot_rustc(paths: &setup::CreusotPaths, args: &Args) -> anyhow::Result<()> {
    args.comment();
    println!("Installing creusot-rustc...");
    let toolchain = setup::toolchain_channel();
    // Ignore error if dir doesn't exist
    let _ = args.remove_dir_all(&paths.data_dir().join("toolchains"));
    // Usually ~/.local/share/creusot/toolchains/nightly-YYYY-MM-DD/
    let toolchain_dir = &setup::toolchain_dir(paths.data_dir(), &toolchain);
    let mut cmd = Command::new("cargo");
    cmd.args(["install", "--path", "creusot-rustc", "--quiet", "--root"]).arg(toolchain_dir);
    args.run(cmd)
}

fn install_tools(paths: &setup::CreusotPaths, args: &Args) -> anyhow::Result<()> {
    args.create_dir_all(&paths.cache_dir())?;
    for (bin, tool) in [
        (ALTERGO, SetupTool::AltErgo),
        (Z3, SetupTool::Z3),
        (CVC4, SetupTool::CVC4),
        (CVC5, SetupTool::CVC5),
    ] {
        if args.external.contains(&tool) {
            // create symbolic links for external tools
            args.symlink_file(get_path(bin.bin, args)?, paths.bin().join(bin.bin.binary_name))?;
        } else {
            // download binaries for builtins
            download(bin, &paths.cache_dir(), &paths.bin(), args)?;
        }
    }
    Ok(())
}

fn install_prelude(paths: &setup::CreusotPaths, args: &Args) -> anyhow::Result<()> {
    args.comment();
    println!("Installing prelude...");
    let out_dir = &paths.why3find_libs().join("packages/creusot/creusot");
    for entry in fs::read_dir(&PathBuf::from("target/creusot/packages/creusot/creusot"))? {
        let entry = entry?;
        assert!(entry.file_type()?.is_file());
        args.copy(&entry.path(), &out_dir.join(&entry.file_name()))?;
    }
    Ok(())
}

fn install_config(paths: &CreusotPaths, args: &Args) -> anyhow::Result<()> {
    // Default why3find.json for `cargo creusot new`.
    args.copy(&PathBuf::from("why3find.json"), &paths.data_dir().join("why3find.json"))?;
    if args.dry_run {
        let mut why3_conf = Command::new("cargo");
        why3_conf.args(["creusot", "why3-conf"]);
        if let Some(parallelism) = args.provers_parallelism {
            why3_conf.args(["--provers-parallelism", &format!("{}", parallelism)]);
        }
        args.run(why3_conf)
    } else {
        // ad hoc code so that the CI job for Why3 tests can get this config without installing cargo-creusot
        setup::generate_why3_conf(paths, args.provers_parallelism)
    }
}

fn get_path(bin: Binary, args: &Args) -> anyhow::Result<PathBuf> {
    let path = bin.detect_path().ok_or(anyhow!(
        "{} not found. Please install {} version {}",
        &bin.display_name,
        &bin.display_name,
        &bin.version
    ))?;
    args.comment();
    println!("Found {} at path: {}", &bin.display_name, &path.display());
    Ok(path)
}

// download helper

pub fn sha256sum(file: &Path) -> anyhow::Result<String> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    let mut f = fs::File::open(file).context("opening file to hash")?;
    std::io::copy(&mut f, &mut hasher)?;
    Ok(hex::encode(hasher.finalize()))
}

fn download_from_url(url: &Url, dest: &Path, args: &Args) -> anyhow::Result<()> {
    const DOWNLOAD_RETRIES: u32 = 1;
    let mut success = false;
    let mut tries: u32 = 0;
    while !success && tries <= DOWNLOAD_RETRIES {
        if tries > 0 {
            eprintln!("Retrying...")
        };
        let mut curl = Command::new("curl");
        curl.arg(url.url).arg("-fLo").arg(dest);
        args.run(curl)?;
        if args.dry_run {
            return Ok(());
        }
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
fn download_from_url_with_cache(
    url: &Url,
    cache_dir: &Path,
    dest: &Path,
    args: &Args,
) -> anyhow::Result<()> {
    let cached_path = cache_dir.join(url.sha256);
    // With --dry-run, skip the checksum which would take a few seconds.
    if !(cached_path.is_file() && (args.dry_run || sha256sum(&cached_path)? == url.sha256)) {
        download_from_url(url, &cached_path, args)?;
    } else {
        args.comment();
        println!("Skipped download (cached)")
    }
    if cached_path != dest {
        args.copy(&cached_path, dest)?;
    }
    Ok(())
}

// download a list [ManagedBinary]s

fn download(
    bin: ManagedBinary,
    cache_dir: &Path,
    dest_dir: &Path,
    args: &Args,
) -> anyhow::Result<()> {
    args.comment();
    print!("Install {} {}...", bin.bin.display_name, bin.bin.version);
    if args.dry_run {
        println!()
    }
    let path = dest_dir.join(bin.bin.binary_name);
    let dl = bin.download;
    dl(bin.url, cache_dir, &path, args)?;
    set_executable(&path)
}

// Z3 releases come as a .zip archive that includes many things. We are only
// interested in the z3 binary, so we extract it from the archive and throw away
// the rest.

fn download_z3_from_url(
    url: &Url,
    cache_dir: &Path,
    dest: &Path,
    args: &Args,
) -> anyhow::Result<()> {
    use zip::read::ZipArchive;
    // just use the zip file stored in the cache
    let zip_path = cache_dir.join(url.sha256);
    download_from_url_with_cache(url, cache_dir, &zip_path, args)?;
    if args.dry_run {
        println!(
            "unzip -jo {} */bin/z3 -d {}",
            zip_path.display(),
            dest.parent().unwrap().display()
        );
    } else {
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

// CVC5 releases come as a .zip archive that includes many things. We are only
// interested in the cvc5 binary, so we extract it from the archive and throw away
// the rest.

fn download_cvc5_from_url(
    url: &Url,
    cache_dir: &Path,
    dest: &Path,
    args: &Args,
) -> anyhow::Result<()> {
    use zip::read::ZipArchive;
    // just use the zip file stored in the cache
    let zip_path = cache_dir.join(url.sha256);
    download_from_url_with_cache(url, cache_dir, &zip_path, args)?;
    if args.dry_run {
        println!(
            "unzip -jo {} */bin/cvc5 -d {}",
            zip_path.display(),
            dest.parent().unwrap().display()
        );
    } else {
        // extract the cvc5 binary from the .zip archive
        let zipfile = std::fs::File::open(&zip_path)?;
        let mut archive = ZipArchive::new(zipfile)?;
        // find out the full path of the cvc5 binary in the archive
        let cvc5_archive_path = archive
            .file_names()
            .find(|s| s.ends_with("/bin/cvc5"))
            .map(String::from)
            .ok_or(anyhow!("did not find a bin/cvc5 binary in the cvc5 release archive"))?;
        let mut cvc5zipfile = archive.by_name(&cvc5_archive_path)?;
        let mut cvc5file = fs::File::create(dest)?;
        std::io::copy(&mut cvc5zipfile, &mut cvc5file)?;
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

#[cfg(test)]
mod tests {
    use super::*;

    fn test_args() -> Args {
        Args {
            external: vec![],
            skip_cargo_creusot: false,
            skip_creusot_rustc: false,
            skip_why3: false,
            skip_why3_conf: false,
            skip_prelude: false,
            skip_extra_tools: false,
            only_build_prelude: false,
            provers_parallelism: None,
            dry_run: false,
        }
    }

    /// Regression test: copying a binary over a broken symlink (e.g. a stale
    /// symlink left by a previous opam-managed install) must succeed.
    /// `fs::copy` follows symlinks on the destination side, so without
    /// removing `dst` first it would fail with "No such file or directory".
    #[test]
    #[cfg(unix)]
    fn copy_over_broken_symlink() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("source");
        let dst = dir.path().join("dest");

        fs::write(&src, b"binary content").unwrap();

        // Simulate a stale opam symlink at the destination.
        std::os::unix::fs::symlink("/nonexistent/path/alt-ergo", &dst).unwrap();
        assert!(!dst.exists(), "symlink should be broken before the copy");

        test_args().copy(&src, &dst).expect("copy over broken symlink should succeed");

        assert_eq!(fs::read(&dst).unwrap(), b"binary content");
    }
}
