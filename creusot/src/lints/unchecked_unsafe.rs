use rustc_session::declare_tool_lint;

declare_tool_lint! {
    /// The `unchecked_unsafe` lint warns when a safe function contains unsafe blocks
    /// but its preconditions are not of the form `mode!().nopanic() ==> _`,
    /// so Creusot can't be sure that the contract guarantees the safety of the function.
    pub(crate) creusot::UNCHECKED_UNSAFE,
    Warn,
    "The safety of this function may not be guaranteed; expected precondition of the form `mode!().nopanic() ==> _`"
}
