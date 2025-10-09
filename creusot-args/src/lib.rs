pub mod options;

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
