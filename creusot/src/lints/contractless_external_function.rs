use rustc_session::declare_tool_lint;

declare_tool_lint! {
    /// The `contractless_external_function` lint warns when calling a function from
    /// another crate that has not been given a specification.
    ///
    /// In this case, creusot will give it an impossible to fulfill specification:
    /// `#[require(false)]`.
    pub(crate) creusot::CONTRACTLESS_EXTERNAL_FUNCTION,
    Warn,
    "No proof that use such a function can be completed"
}
