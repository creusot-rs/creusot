# Logic functions

Functions marked with `#[logic]` can be used in specs and other logical conditions (`requires`/`ensures` and `invariant`), but cannot be called from normal Rust code (the body of a `logic` function is replaced with a panic). Typically, `logic` functions manipulate variables of logical model types such as `Int` and `Seq<Int>` rather than normal Rust types such as `i32` and `&[i32]`. Within a `logic` function, there are two modes: They can freely use logical, non-executable operationsuse ghost functions

- Statements not enclosed by the `pearlite! { ... }` macro can only use normal Rust syntax, but can perform logical operations such as equalities, comparisons, etc. of logical model types such as `Int`. They cannot call non-`logic` functions (raising the syntax error "program code in logic context"). Loops are not currently supported, and see the next section on recursion.
- Within the `pearlite! { ... }` macro, you can additionally use special pearlite syntax such as quantifiers (e.g., `forall<i> ...`) and implications (`... i > 3 ==> i > 2`).

By default, `logic` functions are *opaque* outside of the module they are defined in (in other words, they are only *open* at the module level). When a function is opaque, only its pre- and postconditions are visible. This is useful if the function is only used to express (and prove) that the preconditions imply the postconditions and we do not care about the result (a *lemma*). However, if you do want to use the result in a specification outside of the module (e.g. if you are using it as a *predicate* in one or more contracts), you can mark the function with `#[open]`. The `open` attribute takes an optional argument, similar to `pub`, e.g. you could specify that a function is to be `#[open(super)]` or `#[open(crate)]`.

## Recursion

When you write *recursive* `ghost`, `logic` or `predicate` functions, you have to show that the function terminates.
For that, you can add `#[variant(EXPR)]` attribute, which says that the value of the expression `EXPR` strictly decreases (in a known well-founded order) at each recursive call.
The type of `EXPR` should implement the `WellFounded` trait.

## Prophetic functions

As seen in the chapter on [mutable borrow](./representation_of_types/mutable_borrows.md), a mutable borrow contains a _prophetic_ value, whose value depends on future execution. In order to preserve the soundness of the logic, `#[logic]` functions are not allowed to observe that value: that is, they cannot call the prophetic `^` operator.

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

