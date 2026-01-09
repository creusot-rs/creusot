# Gnome sort

> [!IMPORTANT]
> Get the starting code for this tutorial in the [creusot-rs/tutorial repository](https://github.com/creusot-rs/tutorial).
>
> Open the file [`src/ex1_gnome_sort.rs`](https://github.com/creusot-rs/tutorial/blob/main/src/ex1_gnome_sort.rs).

Gnome sort is a sorting algorithm with the simplicity of a single while loop.

```rust
pub fn gnome_sort(v: &mut [usize])
{
    let mut n = 0;
    while n < v.len() {
        if n == 0 || v[n - 1] <= v[n] {
            n += 1;
        } else {
            v.swap(n - 1, n);
            n -= 1;
        }
    }
}
```

Starting from index `n = 0`, we increment `n` as long as
we encounter successive elements in increasing order.
When we find an element `v[n]` out of order (`v[n] < v[n-1]`),
we insert it into the preceding sorted prefix by repeated swaps of adjacent elements.

## Step 1: Specification

**Write the contract of `gnome_sort`, using the `#[ensures]` attribute.**

There are two postconditions to formalize:

1. The final slice `^v` contains elements in increasing order.
2. The final slice `^v` contains the same elements as the initial slice `v`.

After having written your specification, you should be able to compile the project (with the command `cargo creusot`). But of course the proof attempt will fail (with the command `cargo creusot prove`).

> [!TIP]
>
> - Universal quantification is written as `forall<i>` (or with a type annotation, `forall<i: Int>`). Implication is written as `==>`.
> - To access the elements of a slice in logic, use the view operator `@`. The term `v@` denotes the finite sequence of elements contained in the slice `v`, and `v@[i]` denotes
>     the `i`-th element of that sequence.
> - The second postcondition is just [`(^v)@.permutation_of(v@)`][perm].
>     (Actually spelling this out is rather complicated and besides the point of this tutorial.)

[perm]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.permutation_of

<details>
<summary>Solution</summary>

```rust
#[ensures(forall<i,j> 0 <= i && i < j && j < v@.len() ==> (^v)@[i] <= (^v)@[j])]
#[ensures((^v)@.permutation_of(v@))]
```

</details>

## Step 2: Loop invariant

To help Creusot prove that the contract is valid, we want to write a suitable loop invariant. There will be two clauses to the invariant, mirroring the
desired postconditions we just wrote:

1. The first `n` elements of `v` are in increasing order.
2. The current slice `v` contains the same elements as the *old slice*
    (*i.e.*, the initial value of the slice).

To be able to refer to the *old slice*, **take a snapshot of `v` before entering the loop**:

```rust
let old_v = snapshot!{ v };
```

A snapshot is a purely logical construct. Its value can only be
accessed in specifications. During execution, a snapshot behaves like
the unit `()`.

Now, `old_v` has type `Snapshot<&mut [usize]>`, so we can refer to the
initial value as `**old_v` in Pearlite (one `*` for `Snapshot`,
and one `*` for `&mut`).

**Annotate the `while` loop with its invariant(s), using the `#[invariant]` attribute.**

With this, the command `cargo creusot prove` should succeed.
You have formally verified the functional correctness of a sorting function.

<details>
<summary>Solution</summary>

```rust
#[invariant(forall<i,j> 0 <= i && i < j && j < n@ ==> v@[i] <= v@[j])]
#[invariant(v@.permutation_of((**old_v)@))]
```

</details>

## Step 3: Polymorphism

The function `gnome_sort` is currently restricted to elements of type `usize`.
**Let's generalize `gnome_sort` to elements of any type that implements the comparison operation (`<=`).**
In other words, we can sort slices of any *totally ordered type*.

In Rust, totally ordered types implement the `Ord` trait.
In Creusot, we also require such types `T` to implement the trait
[`DeepModel`][deep-model], and for the associated type `T::DeepModelTy` to
implement [`OrdLogic`][ord-logic], which is the "logical" equivalent of `Ord`:
`OrdLogic` defines the meaning of `<=` in Pearlite.

Although this looks convoluted, this makes it easier to specify and
verify implementations of `Ord` for complex data structures.

With this generalization, we will also need to modify the `#[ensures]` and
`#[invariant]` clauses. Instead of directly comparing elements of the slice
(`v@[i] <= v@[j]`), we will compare their deep models
(`v@[i].deep_model() <= v@[j].deep_model()`).

[ord-logic]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/ord/trait.OrdLogic.html
[deep-model]: https://creusot-rs.github.io/creusot/doc/creusot_std/model/trait.DeepModel.html

<details>
<summary>Solution</summary>

```rust
pub fn gnome_sort<T>(v: &mut [T])
where
    T: Ord + DeepModel,
    T::DeepModelTy: OrdLogic,
{
    /* ... */
}
```

</details>

## Conclusion

We have proved the functional correctness of Gnome sort.
Then we generalized it to sort elements of arbitrary ordered types.

Bonus challenge (non-trivial!): prove the termination of `gnome_sort`. See the [Termination](./termination.md) chapter for more information.
