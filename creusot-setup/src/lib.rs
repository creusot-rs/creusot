use directories::ProjectDirs;
use std::path::{Path, PathBuf};

mod tools;
pub mod tools_versions_urls;
pub use tools::*;

// CAUTION: on MacOS, [config_dir] and [data_dir] are in fact the same directory
pub struct CreusotPaths {
    project_dirs: ProjectDirs,
    why3_conf: PathBuf,
    bin: PathBuf,
}

impl CreusotPaths {
    pub fn config_dir(&self) -> &Path {
        self.project_dirs.config_dir()
    }

    pub fn data_dir(&self) -> &Path {
        self.project_dirs.data_dir()
    }

    pub fn cache_dir(&self) -> &Path {
        self.project_dirs.cache_dir()
    }

    pub fn why3_conf(&self) -> &Path {
        &self.why3_conf
    }

    pub fn bin(&self) -> &Path {
        &self.bin
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

    pub fn binary(&self, path: impl AsRef<Path>) -> PathBuf {
        self.bin().join(path)
    }
}

pub fn creusot_paths() -> CreusotPaths {
    // arguments: qualifier, organization, application
    // unwrap can't fail because Creusot users have a home
    let project_dirs = ProjectDirs::from("", "creusot", "creusot").unwrap();
    CreusotPaths {
        why3_conf: project_dirs.config_dir().join("why3.conf"),
        bin: project_dirs.data_dir().join("bin"),
        project_dirs,
    }
}

pub fn toolchain_dir(data_dir: &Path, toolchain: &str) -> PathBuf {
    data_dir.join("toolchains").join(toolchain)
}

pub fn toolchain_channel() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain"))
        .expect("Expected `cargo-creusot` to be built with a valid toolchain file");
    toolchain["toolchain"]["channel"].as_str().unwrap().to_string()
}
