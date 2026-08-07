# Proof modes

Proof modes track special properties of the execution of a function
which may be required depending on the calling context.
Creusot implements the following modes:

- the `nopanic` mode forbids panics (with some exceptions),
  it is disabled when verifying that a function is safe to call in unverified code;
- the `terminating` mode requires the function to terminate;
- the `ghost` mode is activated by calls in ghost code,
  it enables `nopanic` and `terminating`, with extra restrictions.

Additional modes may appear in the future.

Proof modes are modelled as an implicit parameter to every program function.
It can be named in `#[requires]` and `#[ensures]`[^ensures-mode]
using closure syntax. The status of each mode can be accessed using
a logical method.

[^ensures-mode]: In `#[ensures]`, the postcondition can be a closure with up to two arguments:
    the first is the result and the second is the mode argument.

For example, the following `panic` function can be called
if and only if the `nopanic` mode is disabled:

```rust
#[check(ghost)]
#[requires(|mode| !mode.nopanic())]
fn panic() -> ! {
    // ...
}
```

## `terminates` mode

The `terminates` mode requires a function to terminate.

It is disabled by default: every program function implicitly requires that `mode.terminates()`
be false unless it is marked with `#[check(terminates)]`.

A function marked with `#[check(terminate)]` can use `mode().terminates`
to guard preconditions that ensure only the termination of a function.

In the following example:
- the precondition says that `f(x)` terminates if `0 <= x`,
- the postcondition says that `f(x)` terminates only if `0 <= x` (because
  the function may be called on any input with `mode.terminates()` set to `false`,
  and the postcondition holds whenever it terminates).

```rust
#[check(terminates)]
#[requires(mode.terminates() ==> 0 <= x)]
#[ensures(0 <= x)]
fn f(x: isize) {
    if x != 0 {
        f((x - 1) / 2)
    }
}
```

In more details, the `#[check(terminates)]` attribute does the following:

- it removes the implicit precondition `!mode.terminates()`,
- if the function is recursive, it must have a `#[variant]`
  and only call other terminating functions,
- every loop must also have a `#[variant]`,
- those variants generate side conditions that are guarded by `mode.terminates()`.

## `nopanic` mode

The `nopanic` mode, as its name implies, guards the `std::panic` functions.

```rust
#[check(ghost)]
#[requires(!mode.nopanic())]
fn panic() -> ! {
    // ...
}
```

You normally don't want your functions to panic, but there is one key use case for
disabling this mode: proving the safety of a function that uses unsafe operations in its body.

### Proving safety

In Rust, functions are *safe* by default, meaning that they do not exhibit any undefined behavior.
Unsafe functions are explicitly marked with the `unsafe` keyword, and they have safety conditions that
callers must uphold to avoid undefined behavior.

There is a slight gap between safety and the usual meaning of Creusot contracts.
Safety is the property that a function avoids undefined behavior *for all inputs* of safe functions,
whereas Creusot contracts often feature *nontrivial preconditions* that restrict the domain of inputs
for which the function is intended to be useful.

Proof modes enable you to write preconditions that become trivial (`true`) in the context of proving safety.

The functions with safety proof obligations are **the safe functions that contain unsafe blocks**.
For those functions, Creusot requires that their preconditions are syntactically of the following forms
where `mode` is of course the mode argument that was just bound in the precondition
and `$M` is one of `nopanic`, `terminates`, or `ghost`:

- `!mode.$M()`
- `mode.$M() ==> _`

The current design balances simplicity of implementation with
applicability to known use cases. It is intentionally quite restricted:
it is easy to cook up examples of safe functions that cannot be proved so by Creusot.

<!--
TODO:
- figure out how to deal with closure arguments.
- (longer term) it seems possible to remove this new requirement by instead implicitly inserting
  a `nopanic` premise to all preconditions of safe functions.
-->

## `ghost` mode

Ghost code must terminate normally, thus `ghost` mode also enables `nopanic` and `terminates`,
but that alone is not quite sufficient. In particular, `nopanic` does not prevent some panics
related to resource exhaustion, notably in `Vec` and other collections (cf. the chapter
on [Limitations](limitations.md#some-panics-are-allowed)).
These are forbidden in `ghost` mode.

Similar to `terminates`, `ghost` mode is disabled by default: there is an implicit
precondition that `mode().ghost` be false. This restriction is removed by the
attribute `#[check(ghost)]`.

The attribute `#[check(ghost)]` allows a function to be called in ghost code,
but it is still callable in non-ghost code by default.
You can use a precondition to make a function callable in ghost code only,
so it may call other ghost-only functions:

```rust
#[check(ghost)]
#[requires(mode().ghost)]
fn ghost_new<T>(x: T) -> Ghost<T> {
    // Can only be called in ghost code
    Ghost::new(x)
}
```

Ghost mode is set by function calls inside `ghost!` blocks.

```rust
// Not a ghost function
fn f(x: Ghost<usize>) -> Ghost<usize> {
    // This `ghost!` block enables ghost mode, which enables calling `into_inner`
    ghost!{
        x.into_inner() + 1
    }
}
```

## Proof modes for closures

Just as proof modes are additional implicit arguments to program functions,
they are also present for closures. When you apply a closure, it implicitly
takes a proof mode (for instance, depending on whether you're in a ghost block).
This proof mode is an additional argument to the logic methods `precondition`
and `postcondition`.

If a closure argument is meant to be called with the same mode
as the current function, then we should check its precondition using
the current mode, denoted `mode()`.

```rust
#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
fn apply<A, B>(f: FnOnce(A) -> B, x: A) -> B {
    f(x)
}
```

If a closure argument is meant to be called in ghost code,
then we should check its precondition in ghost mode, denoted `Mode::ghost()`.

```rust
#[requires(|mode| f.precondition(mode.into_ghost(), (x,)))]
#[ensures(|result, mode| f.postcondition(mode.into_ghost(), (x,), result))]
fn apply_ghost<A, B>(f: FnGhost(A) -> B, x: Ghost<A>) -> Ghost<B> {
    ghost! { f(x.into_inner()) }
}
```

Similarly, trait methods can also carry pre- and postconditions depending on proof modes.
This enables us to express that the termination of a function depends on the termination
of unknown functions that it calls.

```rust
/// `my_next` is ghost-callable/terminating if `I::next` is ghost-callable/terminating.
#[check(ghost)]
#[requires(|mode| <I as Iterator>::next.precondition(mode, (i,), result))]
fn my_next<I: Iterator>(i: &mut I) -> Option<<I as Iterator>::Item> {
    next()
}
```
