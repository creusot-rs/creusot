use crate::tools_versions_urls::*;
use anyhow::{anyhow, bail, Context};
use reqwest::blocking::Client;
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

// ----
// we should only need to update the [Binary] definitions below whenever the
// format of a tool binary releases change (unlikely)

pub const WHY3: ExtBinary = ExtBinary {
    display_name: "Why3",
    binary_name: "why3",
    version: WHY3_VERSION,
    detect_version: detect_why3_version,
};

pub const ALTERGO: ExtBinary = ExtBinary {
    display_name: "Alt-Ergo",
    binary_name: "alt-ergo",
    version: ALTERGO_VERSION,
    detect_version: detect_altergo_version,
};

pub const Z3: Binary = Binary {
    display_name: "Z3",
    version: Z3_VERSION,
    install_as: "z3",
    url: &URLS.z3,
    download_with: download_z3_from_url,
};

pub const CVC4: Binary = Binary {
    display_name: "CVC4",
    version: CVC4_VERSION,
    install_as: "cvc4",
    url: &URLS.cvc4,
    download_with: download_from_url_with_cache,
};

pub const CVC5: Binary = Binary {
    display_name: "CVC5",
    version: CVC5_VERSION,
    install_as: "cvc5",
    url: &URLS.cvc5,
    download_with: download_from_url_with_cache,
};

// ----

#[derive(Clone, Copy)]
pub struct Binary {
    pub display_name: &'static str,
    pub version: &'static str,
    install_as: &'static str,
    url: &'static Url,
    download_with: fn(&Client, &Url, &Path, &Path) -> anyhow::Result<()>,
}

#[derive(Clone, Copy)]
pub struct ExtBinary {
    pub display_name: &'static str,
    pub binary_name: &'static str,
    pub version: &'static str,
    detect_version: fn(&Path) -> Option<String>,
}

// download a list [Binary]s

pub fn download_all(bins: &[Binary], cache_dir: &Path, dest_dir: &Path) -> anyhow::Result<()> {
    let client = Client::new();
    for bin in bins {
        println!("Downloading {} {}...", bin.display_name, bin.version);
        let path = dest_dir.join(bin.install_as);
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

pub enum DetectedVersion {
    Good,
    Bad(Option<String>),
}

pub fn detect_binary_path(bin: &ExtBinary) -> Option<PathBuf> {
    use which::which;
    which(bin.binary_name).ok()
}

pub fn detect_binary_version(bin: &ExtBinary, path: &Path) -> DetectedVersion {
    let detect_version = bin.detect_version;
    match detect_version(&path) {
        None => DetectedVersion::Bad(None),
        Some(ver) if ver != bin.version => DetectedVersion::Bad(Some(ver)),
        Some(_) => DetectedVersion::Good,
    }
}

// helpers: why3

fn detect_why3_version(why3: &Path) -> Option<String> {
    let output = Command::new(&why3).arg("--version").output().ok()?;
    let version_full = String::from_utf8(output.stdout).ok()?;
    let version = version_full.strip_prefix("Why3 platform, version ");
    version.map(|ver| {
        let parts: Vec<_> = ver.split(|c| c == '.' || c == '+').collect();
        String::from(&parts[..3].join("."))
    })
}

pub fn generate_why3_conf(
    why3_path: &Path,
    bin_dir: &Path,
    dest_file: &Path,
) -> anyhow::Result<()> {
    println!("Generating a fresh why3 configuration...");
    // create or empty the destination file to avoid getting a warning from why3
    // because it doesn't exist
    {
        let _ = fs::File::create(&dest_file);
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
    Ok(())
}

// helpers: alt-ergo

fn detect_altergo_version(altergo: &Path) -> Option<String> {
    let output = Command::new(&altergo).arg("--version").output().ok()?;
    let out_s = String::from_utf8(output.stdout).ok()?;
    // will be needed for more recent altergo versions
    // out_s.trim_end_matches(char::is_whitespace).strip_prefix("v").map(String::from)
    Some(out_s.trim_end_matches(char::is_whitespace).to_owned())
}

// helpers: Z3

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
