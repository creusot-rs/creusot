use std::path::PathBuf;

use anyhow::anyhow;
use cargo_metadata::{self, Package};
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

fn select_root_crate(m: &cargo_metadata::Metadata) -> Result<&Package> {
    if m.workspace_default_members.is_empty() {
        return Err(anyhow!("can't create mlcfg file, no default workspace"));
    }

    // cargo metadata doesn't specify one particular crate.
    // We consider that the first crate in the list of workspace_default_members will give the name of the file
    let crate_id = &m.workspace_default_members[0];
    let Some(package) = m.packages.iter().find(|p| &p.id == crate_id) else {
        return Err(anyhow!("can't create mlcfg file, no default package"));
    };

    Ok(package)
}

pub(crate) fn make_mlcfg_filename(m: &cargo_metadata::Metadata) -> Result<PathBuf> {
    let root_crate = select_root_crate(m)?;

    // to specify the crate kind in the file name: lib, bin
    if root_crate.targets.is_empty() || root_crate.targets[0].kind.is_empty() {
        return Err(anyhow!("can't create mlcfg file, default package without target"));
    }

    let crate_type = &root_crate.targets[0].kind[0];
    let filename = format!("{}-{}.mlcfg", root_crate.name, crate_type);

    // put the file at the root of the target directory
    Ok(m.target_directory.join(filename).into())
}
