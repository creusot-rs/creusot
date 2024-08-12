# `proof_assert!`

At any point in the code, you may want to insert an arbitrary verification condition. This can be useful:
- For debugging, to ensure that a property indeed holds at a certain point of the program.
- To help the provers in specific cases.

To do this, Creusot gives you the `proof_assert!` macro:

```rust
fn f() {
    // ...
    let x = 1;
    let y = 2;
    proof_assert!(x@ + y@ == 3);
    // ...
}
```

> `proof_assert` must contain a pearlite expression returning a boolean.