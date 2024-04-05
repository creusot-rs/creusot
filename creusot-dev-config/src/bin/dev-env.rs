use anyhow::anyhow;
use std::{env, path::PathBuf};
use which::which;

pub fn main() -> anyhow::Result<()> {
    let paths = creusot_dev_config::paths()?;

    let why3_path = which(&paths.why3)?;
    eprintln!("Using Why3 at: {}", &why3_path.display());
    let why3_dir = PathBuf::from(&why3_path.parent().ok_or(anyhow!("finding why3's location"))?);
    let new_path = match env::var_os("PATH") {
        Some(path) => {
            let mut path_elts = env::split_paths(&path).collect::<Vec<_>>();
            path_elts.insert(0, why3_dir);
            env::join_paths(path_elts)?
        }
        None => env::join_paths([why3_dir].iter())?,
    };
    println!("PATH={:?}; export PATH;", &new_path);

    if let Some(config) = &paths.why3_config {
        eprintln!("Using Why3 config at: {}", config.display());
        println!("WHY3CONFIG='{}'; export WHY3CONFIG;", &config.display());
    }
    Ok(())
}
