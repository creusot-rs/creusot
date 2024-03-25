use rustc_session::declare_tool_lint;

declare_tool_lint! {
    /// Blah Blah
    pub creusot::PRUSTI_ZOMBIE,
    Allow,
    "a type was coerced into a Zombie type"
}

declare_tool_lint! {
    /// Blah Blah
    pub creusot::PRUSTI_FINAL,
    Allow,
    "a dereference was translated to the final operator"
}

declare_tool_lint! {
    /// Blah Blah
    pub creusot::PRUSTI_AMBIGUITY,
    Warn,
    "the translation of a dereference was ambiguous so the current operator was chosen arbitrarily"
}

declare_tool_lint! {
    /// Blah Blah
    pub creusot::PRUSTI_DBG_TY,
    Warn,
    "used for debugging the types of expressions being translated"
}
