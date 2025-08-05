# Termination

By default, Creusot does not require that program functions terminate, which may lead to surprising situations:

```rust
#[ensures(result@ == 42)]
fn nonsense() -> u64 {
    while true {}
    1
}
```

This can be avoided at the cost of more complicated verification, by adding the `check(terminates)` attribute to a function:

```rust
#[check(terminates)]
#[ensures(result@ == 42)]
fn nonsense() -> u64 { // Fails to compile now !
    while true {}
    1
}
```

A function with the `check(terminates)` attribute cannot:

- Call a non-`terminates` function.
- Use a loop construct (`for`, `while`, `loop`). This restriction may be lifted in the future.
- Use simple recursion without the `variant` attribute.

  This means that this function will not be accepted:

  ```rust
  #[check(terminates)]
  fn f(x: u32) -> bool {
      if x == 0 { false } else { f(x - 1) }
  }
  ```

  But this one will (the variant will be checked by why3):

  ```rust
  #[check(terminates)]
  #[variant(x)]
  fn f(x: u32) -> bool {
      if x == 0 { false } else { f(x - 1) }
  }
  ```

- Use mutual recursion, like in the following example:

  ```rust
  #[check(terminates)]
  fn f() { g() } // Error: mutually recursive functions

  #[check(terminates)]
  fn g() { f() }
  ```

## Mutual recursion through traits

Traits complicate the recursion analysis. Indeed, if we have a function like

```rust
trait Tr {
    fn f();
}
fn g<T: Tr>() {
    <T as Tr>::f();
}
```

It isn't possible to know ahead of time which instance of `f` will be called.

Thus, Creusot makes the decision to check recursion at _instantiation time_: the above example compiles, but

```rust
trait Tr {
    fn f();
}
fn g<T: Tr>() {
    <T as Tr>::f();
}

impl Tr for i32 {
    fn f() {
        g::<i32>();
    }
}
```

does not, because we know that `g::<i32>` calls `<i32 as Tr>::f()`, causing a cycle.

## Dependencies

The recursion check explores the body of the functions in the current crate, but it cannot do so with the dependencies, whose function bodies are not visible.

Thus, it assumes two things:

1. The recursion check passed on the dependencies of the current crate.
2. If a function in a dependency has a trait bound, the recursion check pessimistically assumes that all the functions of the trait are called.

Example:

```rust
// dependency/src/lib.rs
trait Tr {
    fn f();
}
fn g<T: Tr>() {
    // It does not matter if `<T as Tr>::f` is called or not, since we cannot see it
}

// lib.rs
impl Tr for i32 {
    fn f() {
        g::<i32>(); // Error !
    }
}
```
