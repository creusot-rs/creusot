# Logic functions

We provide two new attributes on Rust functions: `logic` and `predicate`.

Marked `#[logic]` or `#[predicate]`, a function can be used in specs and other logical conditions (`requires`/`ensures` and `invariant`). They can use ghost functions.
The two attributes have the following difference:

- A `logic` function can freely have logical, non-executable operations, such as quantifiers, logic equalities, etc. Instead, this function can't be called in normal Rust code (the function body of a `logic` function is replaced with a panic).
  You can use pearlite syntax for any part in the logic function by marking that part with the `pearlite! { ... }` macro.
- A `predicate` is a logical function which returns a proposition (in practice, returns a boolean value).

## Recursion

When you write *recursive* `ghost`, `logic` or `predicate` functions, you have to show that the function terminates.
For that, you can add `#[variant(EXPR)]` attribute, which says that the value of the expression `EXPR` strictly decreases (in a known well-founded order) at each recursive call.
The type of `EXPR` should implement the `WellFounded` trait.

## Prophetic functions

As seen in the [model](./model.md) chapter, a mutable borrow contains a _prophetic_ value, whose value depends on future execution. In order to preserve the soundness of the logic, `#[logic]` functions are not allowed to observe that value: that is, they cannot call the prophetic `^` operator.

If you really need a logic function to use that operator, you need to mark it with `#[logic(prophetic)]`/`#[predicate(prophetic)]` instead. In exchange, this function cannot be called from ghost code (unimplemented right now).

A normal `#[logic]` function cannot call a `#[logic(prophetic)]` function.

## Examples

Basic example:

```rust
#[logic]
fn logic_add(x: Int, y: Int) -> Int {
    x + y
}

#[requires(x < i32::MAX)]
#[ensures(result@ == logic_add(x@, 1))]
pub fn add_one(x: i32) -> i32 {
    x + 1
}
```

Pearlite block:

```rust
#[predicate]
fn all_ones(s: Seq<i32>) -> bool {
    pearlite! {
        forall<i: Int> i >= 0 && i < s.len() ==> s[i]@ == 1
    }
}

#[ensures(all_ones(result@))]
#[ensures(result@.len() == n@)]
pub fn make_ones(n: usize) -> Vec<i32> {
    creusot_contracts::vec![1; n]
}
```

Recursion:

```rust
TODO
```

Prophetic:

```rust
TODO
```

<!-- TODO: Explain `#[open(...)]` -->
