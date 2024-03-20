# Invariants

Inside a function, you can attach `invariant` clauses to loops, these are attached on _top_ of the loop rather than inside, like:

```rust
#[invariant(... loop invariant ...)]
while ... { ... }
```

<!-- TODO: Better documentation on `#[invariant]`:

- precise syntax (mention pearlite)
- meaning
- common patterns, examples -->
