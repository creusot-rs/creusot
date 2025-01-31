use crate::tools_versions_urls::*;
use anyhow::{anyhow, bail, Context};
use indoc::writedoc;
use reqwest::blocking::Client;
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

// ----
// we should only need to update the [Binary] definitions below whenever the
// format of a tool binary releases change (unlikely)

pub const WHY3: Binary = Binary {
    display_name: "Why3",
    binary_name: "why3",
    version: WHY3_VERSION,
    detect_version: detect_why3_version,
};

pub const WHY3FIND: Binary = Binary {
    display_name: "why3find",
    binary_name: "why3find",
    version: WHY3FIND_VERSION,
    detect_version: detect_why3find_version,
};

pub const ALTERGO: ManagedBinary = ManagedBinary {
    bin: Binary {
        display_name: "Alt-Ergo",
        binary_name: "alt-ergo",
        version: ALTERGO_VERSION,
        detect_version: detect_altergo_version,
    },
    url: &URLS.altergo,
    download_with: download_from_url_with_cache,
};

pub const Z3: ManagedBinary = ManagedBinary {
    bin: Binary {
        display_name: "Z3",
        binary_name: "z3",
        version: Z3_VERSION,
        detect_version: detect_z3_version,
    },
    url: &URLS.z3,
    download_with: download_z3_from_url,
};

pub const CVC4: ManagedBinary = ManagedBinary {
    bin: Binary {
        display_name: "CVC4",
        binary_name: "cvc4",
        version: CVC4_VERSION,
        detect_version: detect_cvc4_version,
    },
    url: &URLS.cvc4,
    download_with: download_from_url_with_cache,
};

pub const CVC5: ManagedBinary = ManagedBinary {
    bin: Binary {
        display_name: "CVC5",
        binary_name: "cvc5",
        version: CVC5_VERSION,
        detect_version: detect_cvc5_version,
    },
    url: &URLS.cvc5,
    download_with: download_from_url_with_cache,
};

pub const PROVERS: &[ManagedBinary] = &[ALTERGO, Z3, CVC4, CVC5];

// ----

#[derive(Clone, Copy)]
pub struct ManagedBinary {
    pub bin: Binary,
    url: &'static Url,
    download_with: fn(&Client, &Url, &Path, &Path) -> anyhow::Result<()>,
}

#[derive(Clone, Copy)]
pub struct Binary {
    pub display_name: &'static str,
    pub binary_name: &'static str,
    pub version: &'static str,
    detect_version: fn(&Path) -> anyhow::Result<String>,
}

// download a list [ManagedBinary]s

pub fn download_all(
    bins: &[ManagedBinary],
    cache_dir: &Path,
    dest_dir: &Path,
) -> anyhow::Result<()> {
    let client = Client::new();
    for bin in bins {
        println!("Downloading {} {}...", bin.bin.display_name, bin.bin.version);
        let path = dest_dir.join(bin.bin.binary_name);
        let dl = bin.download_with;
        dl(&client, bin.url, cache_dir, &path)?;
        set_executable(&path)?;
    }
    Ok(())
}

// download helper

fn sha256sum(file: &Path) -> anyhow::Result<String> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    let mut f = fs::File::open(file).context("opening file to hash")?;
    std::io::copy(&mut f, &mut hasher)?;
    Ok(hex::encode(hasher.finalize()))
}

fn download_from_url(client: &Client, url: &Url, dest: &Path) -> anyhow::Result<()> {
    const DOWNLOAD_RETRIES: u32 = 1;
    let do_download = || -> anyhow::Result<()> {
        let mut resp = client.get(url.url).send()?;
        let mut file = fs::File::create(dest)?;
        resp.copy_to(&mut file)?;
        Ok(())
    };
    let mut success = false;
    let mut tries: u32 = 0;
    while !success && tries <= DOWNLOAD_RETRIES {
        if tries > 0 {
            eprintln!("Retrying...")
        };
        do_download().with_context(|| format!("downloading {} to {}", url.url, dest.display()))?;
        let file_hash = sha256sum(dest)?;
        if file_hash == url.sha256 {
            success = true
        } else {
            eprintln!("Download failed (wrong hash)");
            let _ = fs::remove_file(dest);
        }
        tries = tries + 1;
    }
    if !success {
        bail!("Download failed after {DOWNLOAD_RETRIES} retries (wrong hash?)")
    };
    Ok(())
}

// looks up [cache_dir] to try to find a cached download; if not, stores the
// result of the download in [cache_dir] (using the hash as the filename).
fn download_from_url_with_cache(
    client: &Client,
    url: &Url,
    cache_dir: &Path,
    dest: &Path,
) -> anyhow::Result<()> {
    let cached_path = cache_dir.join(url.sha256);
    if !(cached_path.is_file() && sha256sum(&cached_path)? == url.sha256) {
        download_from_url(client, url, &cached_path)?;
    }
    if cached_path != dest {
        fs::copy(cached_path, dest)?;
    }
    Ok(())
}

// helpers: external binaries

impl Binary {
    pub fn detect_path(&self) -> Option<PathBuf> {
        use which::which;
        which(self.binary_name).ok()
    }

    pub fn detect_version(&self, path: &Path) -> anyhow::Result<String> {
        (self.detect_version)(path)
    }
}

// helpers: why3

fn detect_why3_version(why3: &Path) -> anyhow::Result<String> {
    let output = run(Command::new(&why3).arg("--version"))?;
    let version_full = String::from_utf8(output.stdout)?;
    match version_full.strip_prefix("Why3 platform, version ") {
        Some(version) => {
            let parts: Vec<_> = version.trim_end().split(|c| c == '.' || c == '+').collect();
            Ok(String::from(&parts[..3].join(".")))
        }
        None => {
            bail!("bad Why3 version: {}", version_full)
        }
    }
}

pub fn generate_why3_conf(
    provers_parallelism: usize,
    why3_path: &Path,
    bin_dir: &Path,
    dest_file: &Path,
) -> anyhow::Result<()> {
    println!("Generating a fresh why3 configuration...");
    {
        use std::io::Write;
        let mut f = fs::File::create(&dest_file)?;
        writeln!(&mut f, "[main]")?;
        writeln!(&mut f, "magic = {WHY3_CONFIG_MAGIC_NUMBER}")?;
        writeln!(&mut f, "running_provers_max = {}", provers_parallelism)?;
    }
    let status = Command::new(why3_path)
        .arg("-C")
        .arg(&dest_file)
        .args(["config", "detect"])
        .envs([("PATH", bin_dir)])
        .status()
        .context("launching 'why3 config detect' on downloaded solvers")?;
    if !status.success() {
        bail!("failed to generate why3's configuration")
    };
    {
        let mut f = fs::OpenOptions::new().append(true).open(&dest_file)?;
        generate_strategy(&mut f)?;
    }

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

// helpers: why3find

pub fn detect_why3find_version(why3find: &Path) -> anyhow::Result<String> {
    let output = run(Command::new(&why3find).arg("--version"))?;
    let version_full = String::from_utf8(output.stdout)?;
    match version_full.strip_prefix("why3find v") {
        Some(version) => {
            let parts: Vec<_> = version.trim_end().split(|c| c == '.' || c == '+').collect();
            Ok(String::from(&parts[..3].join(".")))
        }
        None => bail!("bad Why3find version: {}", version_full),
    }
}

// helpers: alt-ergo

fn detect_altergo_version(altergo: &Path) -> anyhow::Result<String> {
    let output = run(Command::new(&altergo).arg("--version"))?;
    let version_full = String::from_utf8(output.stdout)?;
    let version = version_full.trim_end().strip_prefix("v").map(String::from);
    version.ok_or(anyhow!("bad Altergo version: {}", version_full))
}

// helpers: Z3

// assumes a version string of the form: "Z3 version 4.12.4 - 64 bit"
fn detect_z3_version(z3: &Path) -> anyhow::Result<String> {
    let output = run(Command::new(&z3).arg("--version"))?;
    let version_full = String::from_utf8(output.stdout)?;
    let version = version_full
        .strip_prefix("Z3 version ")
        .and_then(|version| version.split_ascii_whitespace().next().map(String::from));
    version.ok_or(anyhow!("bad Z3 version: {}", version_full))
}

// Z3 releases come as a .zip archive that includes many things. We are only
// interested in the z3 binary, so we extract it from the archive and throw away
// the rest.

fn download_z3_from_url(
    client: &Client,
    url: &Url,
    cache_dir: &Path,
    dest: &Path,
) -> anyhow::Result<()> {
    use zip::read::ZipArchive;
    // just use the zip file stored in the cache
    let zip_path = cache_dir.join(url.sha256);
    download_from_url_with_cache(client, url, cache_dir, &zip_path)?;
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
        let mut z3file = fs::File::create(&dest)?;
        std::io::copy(&mut z3zipfile, &mut z3file)?;
    }
    Ok(())
}

// cvc4

// assumes a version of the form: "This is CVC4 version 1.8 [git HEAD 52479010]\n....."
fn detect_cvc4_version(cvc4: &Path) -> anyhow::Result<String> {
    let output = run(Command::new(&cvc4).arg("--version"))?;
    let version_full = String::from_utf8(output.stdout)?;
    let version = version_full
        .strip_prefix("This is CVC4 version ")
        .and_then(|version| version.split_ascii_whitespace().next().map(String::from));
    version.ok_or(anyhow!("bad CVC4 version: {}", version_full))
}

// cvc5

// assumes a version of the form: "This is cvc5 version 1.0.5 [git ...]\n....."
fn detect_cvc5_version(cvc5: &Path) -> anyhow::Result<String> {
    let output = run(Command::new(&cvc5).arg("--version"))?;
    let version_full = String::from_utf8(output.stdout)?;
    let version = version_full
        .strip_prefix("This is cvc5 version ")
        .and_then(|version| version.split_ascii_whitespace().next().map(String::from));
    version.ok_or(anyhow!("bad CVC5 version: {}", version_full))
}

// cross-platform wrappers

fn set_executable(dest: &Path) -> anyhow::Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&dest)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&dest, perms)?;
    }
    Ok(())
}

pub fn symlink_file<P: AsRef<Path>, Q: AsRef<Path>>(original: P, link: Q) -> std::io::Result<()> {
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

// Wrapper for Command::output(), error is wrapped in anyhow::Error
fn run(cmd: &mut Command) -> anyhow::Result<std::process::Output> {
    cmd.output().map_err(|e| {
        if e.kind() == std::io::ErrorKind::NotFound {
            anyhow!("{:?} not found", cmd.get_program())
        } else {
            anyhow!("{:?}: {}", cmd, e)
        }
    })
}

pub fn why3find_install(why3find: &PathBuf) -> anyhow::Result<()> {
    Command::new(why3find).args(["install", "--global", "prelude"]).status()?;
    Ok(())
}
