use rustc_session::declare_tool_lint;

declare_tool_lint! {
    /// The `opaque_builtin_impl` lint warns when a call resolves to a
    /// compiler-synthesized builtin trait impl that Creusot does not model
    /// (e.g. `Clone`/`Hash` for a tuple or array), on a *concrete* type.
    ///
    /// Such a call is translated abstractly: its result is left unconstrained.
    /// This is sound, but the precision loss is otherwise silent — a downstream
    /// proof that relies on a property of the result (e.g. that a cloned tuple
    /// equals the original) will fail with no obvious cause. The lint makes the
    /// opacity visible at the call site.
    ///
    /// It does not fire for generic parameters (`T::clone` where `T: Clone` is
    /// the ordinary unresolved case) nor for `dyn` types (covered by the
    /// `experimental` lint).
    pub(crate) creusot::OPAQUE_BUILTIN_IMPL,
    Warn,
    "call resolves to an unmodeled builtin trait impl; its result is left unconstrained"
}
