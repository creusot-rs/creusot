# Ghost code

Sometimes, you may need code that will be used only in the proofs/specification, that yet still obeys the typing rules of Rust. In this case, [snapshots](snapshots.md) are not enough, since they don't have lifetimes or ownership.

This is why there exists a separate mechanism: ghost code.

`ghost!` and `Ghost<T>` are the counterparts of `snapshot!` and `Snapshot<T>`.

## `ghost!` blocks

At any point in the code, you may open a `ghost!` block:

```rust
ghost! {
    // code here
}
```

In `ghost!` block, you may write any kind of Rust code, with the following restrictions :

- ghost code must terminate (see [termination](termination.md) for details)
- all functions called must have the `#[check(ghost)]` attribute
- When reading an outer variable, the variable must be of type `Ghost<T>`, or implement `Copy`
- When writing an outer variable, the variable must be of type `Ghost<T>` or `Snapshot<T>`
- The output of the `ghost!` block will automatically be wrapped in `Ghost::new`

Those restriction exists to ensure that ghost code is **erasable**: its presence or absence does not affect the semantics of the actual running program, only the proofs.

## `Ghost<T>`

The `Ghost<T>` type is the type of "ghost data". In Creusot, it acts like a `Box<T>`, while in normal running code, it is an empty type. It has the same `View` as the underlying type, meaning you can use the `@` operator directly.

The only restriction of `Ghost<T>` is that it may not be dereferenced nor created in non-ghost code.

## Examples

- Creating and modifying a ghost variable:

```rust
let mut g = ghost!(50);
ghost! {
    *g *= 2;
};
proof_assert!(g@ == 100);
```

- Calling a function in ghost code:

```rust
#[check(ghost)]
#[requires(*g < i32::MAX)]
#[ensures((^g)@ == (*g)@ + 1)]
fn add_one(g: &mut i32) {
    *g += 1;
}

let mut g = ghost!(41);
ghost! {
    add_one(&mut *g);
};
proof_assert!(g@ == 42);
```

- Using a ghost access token:

```rust
struct Token;

struct Data {
    // ...
}

impl Data {
    fn new() -> (Data, Ghost<Token>) { /* */ }
    fn read(&self, token: &Ghost<Token>) -> T { /* */ }
    fn write(&self, t: T, token: &mut Ghost<Token>) { /* */ }
}
```
