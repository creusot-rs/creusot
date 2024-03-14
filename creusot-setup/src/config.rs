use serde::{Deserialize, Serialize};
use std::{
    fmt, fs,
    path::{Path, PathBuf},
};

// identifies a version of the config file.
// the goal is to avoid silently mis-interpreting a past or future version of
// the config file whenever its format changes.
pub const CURRENT_CONFIG_VERSION: i64 = 1;

// bump CURRENT_CONFIG_VERSION if you change this definition
#[derive(Serialize, Deserialize)]
#[serde(tag = "mode")]
pub enum ToolsConfig {
    #[serde(rename = "managed")]
    Managed {
        why3_path: PathBuf,
        altergo_path: PathBuf,
        z3: String,   // version
        cvc4: String, // version
        cvc5: String, // version
    },
    #[serde(rename = "external")]
    External { why3_path: PathBuf, altergo_path: PathBuf },
}

// bump CURRENT_CONFIG_VERSION if you change this definition
#[derive(Serialize, Deserialize)]
pub struct Config {
    pub tools: ToolsConfig,
}

pub enum Error {
    NotFound,
    Invalid(String),
    WrongVersion(i64),
}

fn get_config_version(cfg: &toml::Value) -> Result<i64, String> {
    cfg.get("version")
        .ok_or("'version' field not found".to_string())?
        .as_integer()
        .ok_or("'version' is not an integer".to_string())
}

impl Config {
    pub fn read_from_file(p: &Path) -> Result<Self, Error> {
        if !p.is_file() {
            return Err(Error::NotFound);
        };
        let s = match fs::read_to_string(p) {
            Err(e) => return Err(Error::Invalid(e.to_string())),
            Ok(s) => s,
        };
        let toml: toml::Value = match toml::from_str(&s) {
            Err(e) => return Err(Error::Invalid(e.to_string())),
            Ok(config) => config,
        };
        let version = match get_config_version(&toml) {
            Err(e) => return Err(Error::Invalid(e)),
            Ok(v) => v,
        };
        if version != CURRENT_CONFIG_VERSION {
            return Err(Error::WrongVersion(version));
        }
        toml.try_into().map_err(|e| Error::Invalid(e.to_string()))
    }

    pub fn write_to_file(&self, p: &Path) -> anyhow::Result<()> {
        let mut toml = toml::Value::try_from(self)?;
        let tbl = toml.as_table_mut().unwrap();
        tbl.insert("version".to_owned(), toml::Value::Integer(CURRENT_CONFIG_VERSION));
        fs::write(p, &toml::to_string(&toml)?)?;
        Ok(())
    }
}

impl fmt::Display for ToolsConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToolsConfig::Managed { why3_path, altergo_path, z3, cvc4, cvc5 } => {
                writeln!(f, "mode: managed")?;
                writeln!(f, "Path to Why3: {}", why3_path.display())?;
                writeln!(f, "Path to Alt-Ergo: {}", altergo_path.display())?;
                writeln!(f, "Z3 version: {z3}")?;
                writeln!(f, "CVC4 version: {cvc4}")?;
                writeln!(f, "CVC5 version: {cvc5}")
            }
            ToolsConfig::External { why3_path, altergo_path } => {
                writeln!(f, "mode: external")?;
                writeln!(f, "Path to Why3: {}", why3_path.display())?;
                writeln!(f, "Path to Alt-Ergo: {}", altergo_path.display())
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::NotFound => write!(f, "No existing Creusot configuration found."),
            Error::Invalid(reason) => write!(f, "Invalid Creusot configuration found: {reason}."),
            Error::WrongVersion(v) => write!(
                f,
                "Existing Creusot configuration found, \
                           but with a different version than expected ({v}, \
                           expected {CURRENT_CONFIG_VERSION})."
            ),
        }
    }
}
