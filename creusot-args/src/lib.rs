pub mod options;

/// Number of threads for rustc's parallel frontend, used unless the user specifies one
/// (with `-Zthreads`, `--jobs-frontend` or `-j`/`--jobs`).
pub const DEFAULT_FRONTEND_THREADS: &str = "-Zthreads=2";

/// Whether `args` (rustc command-line arguments) already set the number of frontend threads.
pub fn sets_frontend_threads<S: AsRef<str>>(args: &[S]) -> bool {
    args.iter().enumerate().any(|(i, arg)| {
        let arg = arg.as_ref();
        arg.starts_with("-Zthreads")
            || (arg == "-Z"
                && args.get(i + 1).is_some_and(|next| next.as_ref().starts_with("threads")))
            || arg.starts_with("--jobs")
            || arg.starts_with("-j")
    })
}

/// Args that activate features needed by creusot.
pub const CREUSOT_RUSTC_ARGS: &[&str] = &[
    "-Cpanic=abort",
    "-Coverflow-checks=off",
    "-Zcrate-attr=feature(register_tool)",
    "-Zcrate-attr=register_tool(creusot)",
    "-Zcrate-attr=feature(stmt_expr_attributes)",
    "-Zcrate-attr=feature(proc_macro_hygiene)",
    "-Zcrate-attr=feature(rustc_attrs)",
    "-Zcrate-attr=feature(unsized_fn_params)",
    "-Znext-solver=globally",
    "-Zno-steal-thir",
    "--allow=internal_features",
    "--cfg",
    "creusot",
];
