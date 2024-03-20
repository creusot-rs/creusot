# Trusted

The `trusted` marker lets Creusot trust the implementation and specs.
More specifically, you can put `#[trusted]` on a function like the following:

```rust
#[trusted]
#[ensures(result == 42u32)]
fn the_answer() -> u32 {
    trusted_super_oracle("the answer to life, the universe and everything")
}
```

TODO: trusted traits
