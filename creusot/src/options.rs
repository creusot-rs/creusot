use crate::arg_value;
use std::collections::HashMap;
use serde_json::from_str;

pub struct Options {
    pub extern_paths: HashMap<String, String>,
    pub metadata_path: Option<String>,
    pub continue_compilation: bool,
    pub has_contracts: bool,
    pub be_rustc: bool,
    pub export_metadata: bool, 
    pub dependency: bool,
    pub output_file: Option<String>,
}

impl Options {
    pub fn from_args_and_env(args: &[String]) -> Self {
        // Check if the crate we are compiling has a dependency on contracts, or if it is the contract crate itself.
        // We use this to disable creusot for dependencies if they don't depend on contracts (since that means they will have no real specification)
        let has_contracts =
            args.iter().any(|arg| arg == "creusot_contracts" || arg.contains("creusot_contracts="));

        let be_rustc = args.iter().any(|arg| arg.contains("--print"));

        // If we're compiling an upstream dependency or we're compiling `creusot_contracts_proc` lets be silent.
        let export_metadata = export_metadata();
        let dependency = arg_value::arg_value(&args, "--cap-lints", |val| val == "allow").is_some();

        let output_file = args.iter().position(|a| a == "-o").map(|ix| args[ix + 1].clone());
        
        let extern_paths = match creusot_externs() {
            Some(val) => from_str(&val).expect("could not parse CREUSOT_EXTERNS"),
            None => HashMap::new(),
        };

        Options {
            has_contracts,
            be_rustc,
            export_metadata,
            dependency,
            output_file,
            continue_compilation: continue_compiler(),
            metadata_path: creusot_metadata_path(),
            extern_paths,
        }
    }
}

fn creusot_externs() -> Option<String> {
    std::env::var_os("CREUSOT_EXTERNS").map(|m| m.to_string_lossy().to_string())

}
fn continue_compiler() -> bool {
    std::env::var_os("CREUSOT_CONTINUE").is_some()
}

fn creusot_metadata_path() -> Option<String> {
    std::env::var_os("CREUSOT_METADATA_PATH").map(|m| m.to_string_lossy().to_string())
}

fn export_metadata() -> bool {
    std::env::var_os("CREUSOT_EXPORT_METADATA").map(|f| f != "false").unwrap_or(true)
}