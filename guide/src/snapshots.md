# Snapshots

A useful tool to have in proofs is the `Snapshot<T>` type (`creusot_std::Snapshot`). `Snapshot<T>` is:

- a zero-sized-type
- created with the `snapshot!` macro
- whose model is the model of `T`
- that can be dereferenced in a logic context.

## Example

They can be useful if you need a way to remember a previous value, but only for the proof:

```rust
#[ensures(array@.permutation_of((^array)@))]
#[ensures(sorted((^array)@))]
pub fn insertion_sort(array: &mut [i32]) {
    let original = snapshot!(*array); // remember the original value
    let n = array.len();
    #[invariant(original@.permutation_of(array@))]
    #[invariant(...)]
    for i in 1..n {
        let mut j = i;
        #[invariant(original@.permutation_of(array@))]
        #[invariant(...)]
        while j > 0 {
            if array[j - 1] > array[j] {
                array.swap(j - 1, j);
            } else {
                break;
            }
            j -= 1;
        }
    }

    proof_assert!(sorted_range(array@, 0, array@.len()));
}

#[logic]
fn permutation_of(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    // ...
}
#[logic]
fn is_sorted(s: Seq<i32>) -> bool {
    // ...
}
```
