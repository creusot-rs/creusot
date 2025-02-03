use std::path::PathBuf;

use anyhow::Error;
use cargo_metadata::{self, CrateType};
use creusot_args::options::CommonOptions;
pub type Result<T> = anyhow::Result<T>;

pub(crate) fn make_cargo_metadata() -> Result<cargo_metadata::Metadata> {
    let mut args = std::env::args().skip_while(|val| !val.starts_with("--manifest-path"));

    let mut cmd = cargo_metadata::MetadataCommand::new();
    match args.next() {
        Some(ref p) if p == "--manifest-path" => {
            cmd.manifest_path(args.next().unwrap());
        }
        Some(p) => {
            cmd.manifest_path(p.trim_start_matches("--manifest-path="));
        }
        None => {}
    };

    cmd.exec().map_err(|e| e.into())
}

pub(crate) fn get_crate(m: &cargo_metadata::Metadata) -> Result<String> {
    let package = m.root_package().ok_or(Error::msg("No root package found"))?;
    let target = package.targets.first().ok_or(Error::msg("No target found"))?;
    let krate_name = target.name.replace("-", "_");
    let krate_type = target.crate_types.first().ok_or(Error::msg("No crate type found"))?;
    let krate_type = if krate_type == &CrateType::Lib { &CrateType::RLib } else { krate_type };
    Ok(krate_name + "_" + &krate_type.to_string())
}

fn get_crate_() -> Result<String> {
    let m = make_cargo_metadata()?;
    get_crate(&m)
}

const OUTPUT_PREFIX: &str = "verif";

pub(crate) fn get_coma(options: &CommonOptions) -> (PathBuf, Option<String>) {
    let coma_src: PathBuf; // coma output file name or directory
    let coma_glob: Option<String>; // glob pattern for all coma files under coma_src
    if let Some(f) = &options.output_file {
        coma_src = f.into();
        coma_glob = None;
    } else if options.stdout {
        coma_src = PathBuf::new(); // don't care, dummy value
        coma_glob = None;
    } else {
        // default to --output-dir=target/creusot
        let mut dir = match &options.output_dir {
            Some(dir) => dir.clone(),
            None => PathBuf::from("."),
        };
        dir.push(OUTPUT_PREFIX);

        let Ok(krate) = get_crate_() else { return (PathBuf::new(), None) };
        if options.monolithic {
            coma_glob = dir.to_str().map(|s| s.to_string() + "/" + &krate + ".coma");
        } else {
            dir.push(krate);
            coma_glob = dir.to_str().map(|s| s.to_string() + "/**/*.coma");
        }
        coma_src = dir;
    }
    (coma_src, coma_glob)
}
