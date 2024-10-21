use std::path::PathBuf;

use cargo_metadata;
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

pub(crate) fn make_coma_target(m: &cargo_metadata::Metadata) -> Result<PathBuf> {
    // put the file at the root of the target directory
    Ok(m.target_directory.join("creusot").into())
}
