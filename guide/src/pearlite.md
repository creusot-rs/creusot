# Pearlite

Pearlite is the language used in:

- contracts (`ensures`, `requires`, `invariant`, `variant`)
- `proof_assert!`
- the `pearlite!` macro

It can be seen as a pure, immutable fragment of Rust which has access to a few additional logical operations and connectives. In practice you have:

- Base Rust expressions: matching, function calls, let bindings, binary and unary operators, tuples, structs and enums, projections, primitive casts, and dereferencing
- Logical Expressions: quantifiers (`forall` and `exists`), logical implication `==>`, _logical_ equality `a == b`, labels <!-- TODO: explain labels -->
- Rust specific logical expressions: access to the **final** value of a mutable reference `^`, access to the [shallow model](./shallow_model.md) of an object `@`

## Logical implication

Since `=>` is already a used token in Rust, we use `==>` to mean implication:

```rust
proof_assert!(true ==> true);
proof_assert!(false ==> true);
proof_assert!(false ==> false);
// proof_assert!(true ==> false); // incorrect
```

## Quantifiers

The logical quantifiers ∀ and ∃ are written `forall` and `exists` in Pearlite:

```rust
#[requires(forall<i: Int> i >= 0 && i < list@.len() ==> list@[i] == 0)]
fn requires_all_zeros(list: &[i32]) {
    // ...
}
```
