use rustc_session::declare_tool_lint;

declare_tool_lint! {
    /// The `result_param` lint warns when a function parameter is named `result`.
    pub(crate) creusot::RESULT_PARAM,
    Warn,
    "`result` as a parameter name is confusing"
}
