# Lemmas and laws

## Lemmas

A _lemma_ is a logical function that is useful because of its pre and postconditions, rather than the value it returns.

For example, suppose that as part of a proof, we want to prove that `x + y > 0 ==> x > 0 || y > 0`.
We can define it as a logical function:

```rust,creusot
#[logic]
#[requires(x + y > 0)]
#[ensures(x > 0 || y > 0)]
fn add_gt_zero(x: Int, y: Int) {}
```

This lemma is easily proved by SMT solvers, so we don't need to give it a body.
Sometimes though, it may be useful to define a body to guide the proof: in this toy example, we could do

```rust,creusot
#[logic]
#[requires(x + y > 0)]
#[ensures(x > 0 || y > 0)]
fn add_gt_zero(x: Int, y: Int) {
    if x > 0 {} else {
        proof_assert!(y >= x + y);
    }
}
```

If `x > 0`, the proof is over; else, we know by arithmetic that `y >= x + y`, so by transitivity of the order it must be `> 0`.

## Lemmas as trait properties

A lot of traits impose greater constraint on their operation than can be seen in the type system.

In this case, additional constraint may be defined as lemmas.
For example, we may want to define a trait for commutative operations:

```rust,creusot
trait Commutative: Sized {
    #[logic]
    fn op(self, other: Self) -> Self;

    #[logic]
    #[ensures(self.op(other) == other.op(self))]
    fn commutative(self, other: Self);
}
```

To ensure commutativity in a way that makes it easy on implementors, we define it as an additional lemma `commutative`.
Implementors of this trait must then prove that commutativity holds for any `self` and `other`.

## Laws

The above example has a potential issue: when using `op`, we don't _automatically_ know that it is commutative: we have to use the lemma first, to import it into the proof context:

```rust,creusot
#[logic]
fn foo<T: Commutative>(x: T, y: T) {
    let z = x.op(y);
    // let _ = x.commutative(y);
    proof_assert!(z == y.op(x)); // does not work without uncommenting the above line
}
```

To make this easier, we can define commutativity as a _law_: a logical function that will get imported into the context whenever a function in the same trait is used.

```rust,creusot
trait Commutative: Sized {
    #[logic]
    fn op(self, other: Self) -> Self;

    #[logic(law)]
    #[ensures(self.op(other) == other.op(self))]
    fn commutative(self, other: Self);
}

#[logic]
fn foo<T: Commutative>(x: T, y: T) {
    let z = x.op(y);
    proof_assert!(z == y.op(x)); // Works!
}
```
