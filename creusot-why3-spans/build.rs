use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;

fn cmd_output(program: &str, args: &[&str]) -> String {
    let out = Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to run `{program}`: {e}"));
    assert!(
        out.status.success(),
        "`{program} {}` failed:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn ocamlfind_query(package: &str) -> String {
    cmd_output("ocamlfind", &["query", package])
}

/// Ask ocamlfind for the full `ocamlopt` link command for `why3` (including
/// all transitive dependencies) and return the argument list — everything
/// after the leading compiler name token.
///
/// Using `-only-show` means ocamlfind prints the command it *would* run
/// without actually running it.  This gives us the correct `-I` flags and
/// `.cmxa` paths for all transitive dependencies (including optional ones
/// such as `camlzip`/`zip` that vary between installations) in the right
/// order, regardless of OCaml version or switch layout.
fn ocamlfind_link_args() -> Vec<String> {
    let line = cmd_output(
        "ocamlfind",
        &[
            "ocamlopt",
            "-package", "why3",
            "-linkpkg",
            "-predicates", "native",
            "-only-show",
        ],
    );
    // The output is a single line like:
    //   ocamlopt -I /path/to/foo -I /path/to/bar foo.cmxa bar.cmxa ...
    // (On some installations the compiler is `ocamlopt.opt` instead of
    // `ocamlopt`; either way it is exactly one whitespace-separated token.)
    // We drop that first token and return the rest.
    line.split_whitespace()
        .skip(1)
        .map(str::to_owned)
        .collect()
}

/// Scan a directory for `lib*.a` files and emit `cargo:rustc-link-lib=static=<stem>`
/// for each one found, skipping OCaml runtime archives (handled separately).
fn emit_static_libs_in_dir(dir: &Path, already_emitted: &mut HashSet<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with("lib") && name.ends_with(".a") {
            // Strip "lib" prefix and ".a" suffix to get the link name.
            let stem = &name[3..name.len() - 2];
            // Skip OCaml runtime archives — handled explicitly below.
            if matches!(
                stem,
                "asmrun" | "asmrun_pic" | "asmrund" | "asmruni"
                | "camlrun" | "camlrun_pic" | "camlrund" | "camlruni"
                | "threads" | "threadsnat"
            ) {
                continue;
            }
            if already_emitted.insert(stem.to_owned()) {
                println!("cargo:rustc-link-lib=static={stem}");
            }
        }
    }
}

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let stub_dir = manifest.join("ocaml-stub");

    // ------------------------------------------------------------------
    // 1. Resolve key paths via ocamlfind / ocamlopt
    // ------------------------------------------------------------------
    let why3_dir          = ocamlfind_query("why3");
    let ocaml_runtime_dir = cmd_output("ocamlopt", &["-where"]);

    // Derive OCAMLPATH for dune: why3 lives at <switch>/lib/why3/, so the
    // switch lib dir is the parent of why3_dir.
    let switch_lib_dir = PathBuf::from(&why3_dir)
        .parent()
        .expect("why3_dir has no parent")
        .to_path_buf();

    // ------------------------------------------------------------------
    // 2. Build the OCaml stub with dune
    // ------------------------------------------------------------------
    let status = Command::new("dune")
        .arg("build")
        .current_dir(&stub_dir)
        .env("OCAMLPATH", &switch_lib_dir)
        .status()
        .expect("failed to run `dune build`");
    assert!(status.success(), "`dune build` failed");

    // ------------------------------------------------------------------
    // 3. Produce the combined OCaml object with ocamlopt -output-obj
    //
    //    We ask ocamlfind for the complete, ordered list of -I flags and
    //    .cmxa archives needed to link why3 and all its transitive
    //    dependencies (including optional ones like camlzip/zip).  We
    //    prepend -I for the stub's build directory so ocamlopt can find
    //    vc_spans_stub.cmi, then append the stub's own .cmx.
    // ------------------------------------------------------------------
    let out_obj        = stub_dir.join("vc_spans_all.o");
    let stub_cmx       = stub_dir
        .join("_build/default/.vc_spans_stub.objs/native/vc_spans_stub.cmx");
    let stub_build_dir = stub_dir.join("_build/default");

    let mut link_args = vec![
        "-output-obj".to_owned(),
        "-o".to_owned(), out_obj.to_str().unwrap().to_owned(),
        // The stub's build dir must come first so its .cmi takes precedence.
        "-I".to_owned(), stub_build_dir.to_str().unwrap().to_owned(),
    ];

    // Append all -I and .cmxa args from ocamlfind (transitive why3 deps).
    link_args.extend(ocamlfind_link_args());

    // Finally add the stub .cmx itself.
    link_args.push(stub_cmx.to_str().unwrap().to_owned());

    let status = Command::new("ocamlopt")
        .args(&link_args)
        .status()
        .expect("failed to run `ocamlopt -output-obj`");
    assert!(status.success(), "`ocamlopt -output-obj` failed");

    // ------------------------------------------------------------------
    // 4. Compile the combined object into a static archive for Cargo
    // ------------------------------------------------------------------
    cc::Build::new()
        .object(&out_obj)
        .compile("vc_spans_ocaml_all");

    // ------------------------------------------------------------------
    // 5. Link C-level dependencies
    //
    //    Strategy: for every unique parent directory of a .cmxa that
    //    ocamlfind listed, add it as a rustc-link-search path and scan it
    //    for lib*.a C stub archives.  This automatically handles:
    //      - libunix.a / libcamlstr.a  (OCaml stdlib, OCaml 4.x flat layout)
    //      - lib/ocaml/unix/libunix.a  (OCaml 5.x subdirectory layout)
    //      - libzarith.a               (zarith)
    //      - libcamlzip.a              (camlzip/zip, if installed)
    //      - any other optional C stubs
    //    We also add the OCaml runtime dir for libasmrun.a.
    // ------------------------------------------------------------------

    // Collect unique .cmxa parent directories from the ocamlfind output.
    let link_args_for_scan = ocamlfind_link_args();
    let mut cmxa_dirs: Vec<PathBuf> = Vec::new();
    let mut seen_dirs: HashSet<PathBuf> = HashSet::new();
    for arg in &link_args_for_scan {
        if arg.ends_with(".cmxa") {
            if let Some(parent) = Path::new(arg).parent() {
                let p = parent.to_path_buf();
                if seen_dirs.insert(p.clone()) {
                    cmxa_dirs.push(p);
                }
            }
        }
    }

    // Always include the OCaml runtime directory (for libasmrun.a).
    let runtime_dir = PathBuf::from(&ocaml_runtime_dir);
    if seen_dirs.insert(runtime_dir.clone()) {
        cmxa_dirs.push(runtime_dir);
    }

    // Emit link-search and scan for C stubs.
    let mut emitted: HashSet<String> = HashSet::new();
    for dir in &cmxa_dirs {
        println!("cargo:rustc-link-search=native={}", dir.display());
        emit_static_libs_in_dir(dir, &mut emitted);
    }

    // The OCaml native runtime itself.
    println!("cargo:rustc-link-lib=static=asmrun");
    println!("cargo:rustc-link-lib=threads");

    // System libraries that OCaml C stubs depend on.
    println!("cargo:rustc-link-lib=gmp");    // zarith → GMP
    println!("cargo:rustc-link-lib=z");      // camlzip → zlib
    println!("cargo:rustc-link-lib=m");
    println!("cargo:rustc-link-lib=dl");
    println!("cargo:rustc-link-lib=pthread");

    // Export all symbols so dynamically-loaded OCaml plugins (.cmxs) can
    // resolve references back into the statically-linked OCaml runtime.
    println!("cargo:rustc-link-arg=-Wl,-export-dynamic");

    println!("cargo:rerun-if-changed=ocaml-stub/vc_spans_stub.ml");
    println!("cargo:rerun-if-changed=ocaml-stub/dune");
    println!("cargo:rerun-if-changed=build.rs");
}
