# Known limitations

Formal verification provides strong guarantees about your code.
Nevertheless, it is important to be aware of the limits of what one has specified.
Creusot users should take note of the following limitations.

## Some panics are allowed

The `Vec` methods that increase capacity (`push`, `insert`, `extend`, etc.)
panic if the capacity overflows. The current contracts in `creusot-contracts`
do not prevent this.

Because `Vec` is such a fundamental type, bounding
its length is quite cumbersome. Moreover, you will probably run out of memory
(another kind of failure that Creusot does not prevent) before the capacity overflows.
There remains one notable blind spot: a `Vec` of a zero-sized type enables
triggering this panic quite easily.

## Architecture specificity

Creusot compiles code for some given target architecture,
so the resulting proofs are only valid for that architecture.

An important consequence is that the sizes of many types
are constants which depend on the architecture or compiler optimizations.
In particular, this affects the value of `usize::MAX` and the sizes of
`repr(Rust)` types. The latter are technically unspecified by
[The Rust Reference: Type Layout][rust-layout].

[rust-layout]: https://doc.rust-lang.org/reference/type-layout.html