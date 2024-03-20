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

## An aside on models

When writing specifications, the language used is similar to, but not exactly Rust. It is called _Pearlite_.

In Pearlite, types are the _logical_ types: we don't have `i32`, `Vec` or `HashMap`, but `Int` (mathematical integer, unbounded), `Seq` (sequence of objects) and `Map` (mapping of objects).

Additionally, we cannot use most functions that we are accustomed to, like `Vec::len`, because they are not purely logical functions. To get around this, types can define their **model**, which is their equivalent in the logical world : we can then call functions and methods on these logical types.

In this case, the model of `&[i32]` is a sequence `Seq<i32>`: we access this model by using the `@` suffix operator.

To learn more, see the chapters on [models](TODO) and [Pearlite](./pearlite.md).

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

Note that we can index a `Seq<i32>` to get a `i32`.
