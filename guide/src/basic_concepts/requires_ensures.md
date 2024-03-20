# requires and ensure

Most of what you will be writing with creusot will be `requires` and `ensures` clauses. That is: **preconditions** and **postconditions**.

Together, those form the **contract** of a function. This is in essence the "logical signature" of your function: when analyzing a function, only the contract of other functions is visible.

## Preconditions with `requires`

A _precondition_ is an assertion that must hold when entering the function. For example, the following function accesses a slice at index `0`:

```rust
fn head(v: &[i32]) -> i32 {
    v[0]
}
```

So we must require that the slice has at least one element:

```rust
#[requires(v@.len() >= 1)]
fn head(v: &[i32]) -> i32 {
    v[0]
}
```

Note the **shallow model** (`@`) operator: it is needed to convert the Rust type `&[i32]` to a logical type `Seq<i32>`. Else, we could not call `[T]::len`, which is a program function (and not a logical one).

To learn more, see the chapter on [Pearlite](../pearlite.md) and [ShallowModel](../shallow_model.md).

## Postconditions with `ensures`

A _postcondition_ is an assertions that is proven true at the end of the function. The return value of the function can be accessed via the `result` keyword.

In the case of the example above, we want to assert that the returned integer is the first of the slice:

```rust
#[requires(v@.len() >= 1)]
#[ensures(v@[0] == result)]
fn head(v: &[i32]) -> i32 {
    v[0]
}
```

Note that we:
- use the `@` operator on the slice to get a `Seq<i32>`
- we can then index this `Seq<i32>` to get a `i32`.
