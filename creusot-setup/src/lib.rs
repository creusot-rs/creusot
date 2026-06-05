use anyhow::Result;
use directories::ProjectDirs;
use std::{
    env, fs, io,
    path::{Path, PathBuf},
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

    pub fn creusot_why3_conf(&self) -> PathBuf {
        self.data_dir().join("creusot_why3.conf")
    }

    pub fn user_why3_conf(&self) -> PathBuf {
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

    pub fn why3find_libs(&self) -> PathBuf {
        self.data_dir().join("share/why3find")
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

/// Update `$XDG_CONFIG_HOME/creusot/why3.conf`:
/// - generate it if it doesn't exist (this mainly sets the `running_provers_max` setting);
/// - otherwise remove any `[partial_prover]` and `[strategy]` (fix previous installations to upgrade to version 0.12) FIXME: don't do this fix after 0.12
pub fn update_why3_conf(paths: &CreusotPaths, parallelism: Option<usize>) -> Result<()> {
    let why3_conf = paths.user_why3_conf();
    if fs::exists(&why3_conf).unwrap_or(false) {
        let contents = fs::read_to_string(&why3_conf)?;
        let mut lines = contents.lines();
        let mut output = String::new();
        let mut changed = false;
        while let Some(line) = lines.next() {
            // Drop [partial_prover] and [strategy] sections, delimited by empty line
            if line == "[partial_prover]" || line == "[strategy]" {
                changed = true;
                let _ = (&mut lines).skip_while(|l| !l.is_empty()).next();
            } else {
                output += line;
                output += "\n";
            }
        }
        if changed {
            println!("Refreshing {}", why3_conf.display());
            fs::write(&why3_conf, output)?;
        }
    } else {
        println!("Generating {}", why3_conf.display());
        fs::create_dir_all(paths.config_dir())?;
        let mut f = fs::File::create(why3_conf)?;
        write_default_why3_conf(&mut f, parallelism)?;
    }
    Ok(())
}

pub fn write_default_why3_conf(f: &mut impl io::Write, parallelism: Option<usize>) -> Result<()> {
    let parallelism = parallelism.unwrap_or_else(default_provers_parallelism);
    write!(
        f,
        r#"[main]
magic = 14
running_provers_max = {parallelism}
memlimit = 1000
timelimit = 5.000000
"#
    )?;
    Ok(())
}

pub fn default_provers_parallelism() -> usize {
    match std::thread::available_parallelism() {
        Ok(n) => n.get(),
        Err(_) => 1,
    }
}
