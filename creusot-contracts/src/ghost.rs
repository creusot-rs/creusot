mod ghost_box;
mod ghost_map;
mod ghost_vec;

/// A type that can be used in `ghost` context.
///
/// This type may be used to make more complicated proofs possible. In particular, some
/// proof may need a notion of non-duplicable token to carry around.
///
/// Conceptually, a `GhostBox<T>` is a pointer to an item of type `T` that resides in
/// a special "ghost" heap. This heap is innacessible from normal code, and `GhostBox`
/// values cannot be used to influence the behavior of normal code.
///
/// This box can be dereferenced in a `ghost` block:
/// ```compile_fail
/// let b: GhostBox<i32> = GhostBox::new(1);
/// ghost! {
///     let value: i32 = *b;
///     // use value here
/// }
/// let value: i32 = *b; // compile error !
/// ```
pub use ghost_box::GhostBox;
pub use ghost_map::GhostMap;
pub use ghost_vec::GhostVec;
