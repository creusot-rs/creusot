# Prophetic functions

As seen in the chapter on [mutable borrow](../representation_of_types/mutable_borrows.md), a mutable borrow contains a _prophetic_ value, whose value depends on future execution. In order to preserve the soundness of the logic, `#[logic]` functions are not allowed to observe that value: that is, they cannot call the prophetic `^` operator.

If you really need a logic function to use that operator, you need to mark it with `#[logic(prophetic)]` instead. In exchange, this function cannot be called from `snapshot!`.

A normal `#[logic]` function cannot call a `#[logic(prophetic)]` function.
