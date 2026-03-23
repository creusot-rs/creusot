# Termination

## Motivations

There are several reasons why Creusot cares about termination:

- Termination of logic functions (in Pearlite) is crucial for soundness. Otherwise you could prove `false` as follows:

    ```rust
    #[logic]
    #[ensures(false)]
    fn falso() {
        falso()
    }
    ```

- Termination of ghost program functions is also necessary for soundness.
  Erasing ghost code must not change the observable behavior of the program.

- Termination of non-ghost program functions is optional, but desirable.

  - By default, we prove *partial correctness*: for all inputs satisfying the precondition,
    **if** the function terminates, **then** its postcondition holds.

  - Adding the attribute `#[check(terminates)]` changes the goal to *total correctness*:
    for all inputs satisfying the precondition, the function terminates **and** its postcondition holds.

  Total correctness of non-ghost programs is opt-in because it is often cumbersome
  (requiring `#[variant]` annotations, no support for mutually recursive functions (yet)...)
  and sometimes significantly harder than partial correctness.

## Terminating program functions: `#[check(terminates)]`

Non-terminating functions may lead to surprising situations:

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
- Use direct recursion or loops without the `variant` attribute.

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

## Termination check in detail

To ensure that declarations are well-defined:

1. we check recursion between types;
2. we check recursion between terminating functions: logic functions and program functions marked `#[check(ghost)]` or `#[check(terminates)]`;
3. in terminating program functions, we check that all loops have variants.

For steps 1 and 2, we construct two dependency graphs of items.
For the type recursion check (step 1), the graph contains types, traits, and impls.
For the function recursion check (step 2), the graph contains functions and impls.
These graphs contain an edge from item A to item B if A mentions B.
Each strongly connected component in that graph is either:

- a single item with no edge to itself, that is a non-recursive item which
  requires no further check: it is well-defined if all of its dependencies are well-founded;
- otherwise, the strongly connected component is a *recursive group*,
  and we have to look at the kind of items it contains.

### Recursive types and strict positivity

In the definition of a recursive type, other types from its recursive group
can only appear in *strictly positive* positions.

At the moment, this allows the defined type to occur only in a field type,
either directly or under `Box`, `&`, or `&mut`. For example:

```rust
pub enum Peano {
    Zero,
    Suc(Box<Peano>), // Peano in strictly positive position ==> OK
}
```

<!--

FIXME: Relax the requirements of strict positivity. Creusot still rejects the following example
(not in the "recursive type check" but in later passes).

In the example above, the first argument of `Mapping<_, _>` is not strictly positive.

On the other hand, the second argument of `Mapping<_, _>` is strictly positive,
so the following recursive type is legal:

```rust
pub enum Tree {
    Leaf,
    Node(Mapping<Int, Tree>),
}
```

-->

There is some experimental support for allowing recursive occurrences through other type constructors.
For example, the argument of `Option<_>` is strictly positive, allowing this type:

```rust
pub enum List<T>(T, Option<Box<List<T>>>);
```

The attribute `#[trusted(positive(T))]` can be used on a `struct` or `enum`
to postulate that certain arguments are strictly positive.

#### Counterexample

Recursive types are indeed a possible source of unsoundness if left unchecked.

The standard counterexample is that a type `L` which is equivalent to `L -> bool`
(written `Mapping<L, bool>` in Creusot) easily leads to a contradiction
without writing an explicitly recursive function:

```rust
// This type is rejected by Creusot,
// otherwise we could prove a contradiction via the function below.
pub struct L(Mapping<L, bool>);

#[logic]
#[ensures(result == !result)] // false!
pub fn infinity() -> bool {
    pearlite! {
        let suc: Mapping<L, bool> = |f: L| !f.0[f];
        suc[L(suc)]
    }
}
```

### Recursive traits: not allowed

A trait cannot belong to a recursive group.
In other words, a trait must not mention itself in its supertrait bounds
or in the bounds of its methods.

#### Counterexample

A proof of `false` using a recursive trait:

```rust
pub trait Tr<T>: Sized {
    #[logic]
    #[ensures(false)]
    fn f(&self, x: &T) where Self: Tr<Self>;
}

impl<U> Tr<i32> for U {
    #[logic]
    #[ensures(false)]
    fn f(&self, x: &i32) where Self: Tr<Self> {
        self.f(self)
    }
}

#[logic]
#[ensures(false)]
fn g() {
    1i32.f(&1i32)
}
```

### Recursive associated types: not allowed

These corresponds to impl items in the type dependency graph.

#### Counterexample

While the Rust type checker already forbids some recursive associated types,
it still allows a form of indirect recursion.
Those are subsequently rejected by Creusot:

```rust
trait P {
    type A;
}

// This alone is not recursive,
// but we must remain careful about how `T: P` is instantiated.
struct B<T: P>(<T as P>::A);

struct Dummy;

impl P for Dummy {
    // This associated type is recursive through the instantiation of `B`.
    type A = Mapping<B<Dummy>, bool>;
}
```

If this were accepted by Creusot, the associated type `Dummy::A` would be equivalent to
`Mapping<Dummy::A, bool>`, which would be unsound as explained in a [previous counterexample](#counterexample).

### Recursive functions

Functions that must terminate are `#[logic]` functions and
program functions annotated with `#[check(ghost)]` or `#[check(terminates)]`.

Currently, mutually recursive functions are not supported.

A recursive function must have a variant (a quantity that decreases at every recursive call)
which implements a [`WellFounded`][well-founded] relation.
Variants are given using the `#[variant(_)]` attribute.

Similarly, within a terminating program function, all loops must also have a `#[variant(_)]`.

The `#[trusted(terminates)]` attribute can be used to disable termination checking
for a function, while allowing calling it in other `#[check(terminates)]` function.

[well-founded]: https://doc.creusot.rs/creusot_std/logic/trait.WellFounded.html

### Mutual recursion through traits

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

### Trait impl methods with bounds

When termination checking a trait impl method, we use the bounds from its trait definition.

#### Counterexample

In the following example, the call `self.f()` will be checked in an environment
without the `i32: Tr` bound of the enclosing function, because it is not present
in the declaration of `f` in `trait Tr`.

```rust
pub trait Tr {
    #[logic]
    #[ensures(false)]
    fn f(self) -> Self;
}

impl Tr for i32 {
    #[logic]
    #[ensures(false)]
    fn f(self) -> Self where i32: Tr {
        self.f()
    }
}

#[logic]
#[ensures(false)]
pub fn contra() -> i32 {
  0i32.f()
}
```
