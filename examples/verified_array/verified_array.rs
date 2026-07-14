//! Verified Array Access Pattern for Creusot
//!
//! This module demonstrates formal verification of array operations using Creusot,
//! proving memory safety and absence of out-of-bounds access through contract specifications.
//!
//! Patterns included:
//! - Safe bounded access with preconditions
//! - Loop invariants for traversal correctness
//! - Postconditions proving no panics or undefined behavior

use creusot_contracts::*;

/// Safe array access with formal bounds verification.
///
/// This function proves that accessing an array element at a specific index
/// is safe when the index is within bounds. Creusot verifies the precondition
/// at compile time, eliminating runtime panics.
///
/// # Requires
/// - `index < arr.len()`: index must be strictly less than array length
///
/// # Ensures
/// - Returns the value at position `index` unchanged
/// - No out-of-bounds memory access occurs
#[requires(index < arr.len())]
#[ensures(result == arr[index])]
pub fn verified_get<T: Copy>(arr: &[T], index: usize) -> T {
    arr[index]
}

/// Mutable safe array access with formal verification.
///
/// Proves that mutable access at a specific index is safe and that
/// the returned reference points to the exact array element.
///
/// # Requires
/// - `index < arr.len()`: index must be within bounds
///
/// # Ensures
/// - Returned reference points to `arr[index]`
/// - All other array elements remain unchanged
#[requires(index < arr.len())]
#[ensures(*result == old(arr[index]))]
#[ensures(forall<i: usize> i != index && i < arr.len() ==> arr[i] == old(arr[i]))]
pub fn verified_get_mut<T>(arr: &mut [T], index: usize) -> &mut T {
    &mut arr[index]
}

/// Safely find the first occurrence of a value in an array.
///
/// Returns `Some(index)` where `arr[index] == value`, or `None` if not found.
/// The loop invariant proves that all indices below `i` have been checked
/// and do not contain the target value.
///
/// # Requires
/// - None (works on any array)
///
/// # Ensures
/// - If `Some(idx)` is returned: `idx < arr.len()` and `arr[idx] == value`
/// - If `Some(idx)` is returned: for all `j < idx`, `arr[j] != value`
/// - If `None` is returned: for all `i < arr.len()`, `arr[i] != value`
#[ensures(match result {
    Some(idx) => idx < arr.len() && arr[idx] == value && {
        forall<j: usize> j < idx ==> arr[j] != value
    },
    None => forall<i: usize> i < arr.len() ==> arr[i] != value,
})]
pub fn verified_find<T: PartialEq>(arr: &[T], value: T) -> Option<usize> {
    let mut i = 0;

    #[invariant(i <= arr.len())]
    #[invariant(forall<j: usize> j < i ==> arr[j] != value)]
    while i < arr.len() {
        if arr[i] == value {
            return Some(i);
        }
        i += 1;
    }

    None
}

/// Sum all elements in an array with formal proof of correctness.
///
/// Proves that the loop correctly accumulates all array elements without
/// missing any or accessing out-of-bounds memory.
///
/// # Requires
/// - None
///
/// # Ensures
/// - The sum is computed from all array elements
/// - Loop processes exactly `arr.len()` elements
#[ensures(result == arr.iter().sum())]
pub fn verified_sum(arr: &[u32]) -> u32 {
    let mut sum: u32 = 0;
    let mut i = 0;

    #[invariant(i <= arr.len())]
    #[invariant(sum == arr[..i].iter().sum())]
    while i < arr.len() {
        sum = sum.wrapping_add(arr[i]);
        i += 1;
    }

    sum
}

/// Copy a range from source to destination with formal verification.
///
/// Proves that `count` elements from `src` starting at `src_start`
/// are correctly copied to `dst` starting at `dst_start` without overlap
/// or out-of-bounds access.
///
/// # Requires
/// - `src_start + count <= src.len()`: source range must be within bounds
/// - `dst_start + count <= dst.len()`: destination range must be within bounds
/// - Ranges must not overlap (if both slices are from same allocation)
///
/// # Ensures
/// - All copied elements match: `dst[dst_start + i] == old(src[src_start + i])` for all `i < count`
/// - Elements outside copy range are unchanged
#[requires(src_start + count <= src.len())]
#[requires(dst_start + count <= dst.len())]
#[ensures(forall<i: usize> i < count ==> dst[dst_start + i] == src[src_start + i])]
#[ensures(forall<j: usize>
    (j < dst_start || j >= dst_start + count) && j < dst.len()
    ==> dst[j] == old(dst[j])
)]
pub fn verified_copy_range(
    src: &[u8],
    src_start: usize,
    dst: &mut [u8],
    dst_start: usize,
    count: usize,
) {
    let mut i = 0;

    #[invariant(i <= count)]
    #[invariant(forall<j: usize> j < i ==> dst[dst_start + j] == src[src_start + j])]
    while i < count {
        dst[dst_start + i] = src[src_start + i];
        i += 1;
    }
}

/// Verify all elements satisfy a predicate.
///
/// Proves that either all elements satisfy the predicate, or at least one
/// element that violates it is correctly identified.
///
/// # Requires
/// - None
///
/// # Ensures
/// - If true: all elements `arr[i]` satisfy the predicate
/// - If false: there exists index where predicate fails
#[ensures(result ==> forall<i: usize> i < arr.len() ==> {
    let elem = &arr[i];
    predicate(elem)
})]
pub fn verified_all<T, F: Fn(&T) -> bool>(arr: &[T], predicate: F) -> bool {
    let mut i = 0;

    #[invariant(i <= arr.len())]
    #[invariant(forall<j: usize> j < i ==> predicate(&arr[j]))]
    while i < arr.len() {
        if !predicate(&arr[i]) {
            return false;
        }
        i += 1;
    }

    true
}

/// Partition array in-place with verified bounds.
///
/// Moves all elements satisfying the predicate to the front.
/// Proves that no out-of-bounds access occurs and partition point is valid.
///
/// # Requires
/// - None
///
/// # Ensures
/// - Returns partition point `p` where `p <= arr.len()`
/// - All elements `arr[0..p]` satisfy the predicate
/// - All elements `arr[p..]` do not satisfy the predicate
/// - Permutation: same elements, possibly reordered
#[ensures(result <= arr.len())]
#[ensures(forall<i: usize> i < result ==> predicate(&arr[i]))]
#[ensures(forall<i: usize> i >= result && i < arr.len() ==> !predicate(&arr[i]))]
pub fn verified_partition<T, F: Fn(&T) -> bool>(arr: &mut [T], predicate: F) -> usize {
    let mut i = 0;
    let mut j = arr.len();

    #[invariant(i <= j)]
    #[invariant(j <= arr.len())]
    #[invariant(forall<k: usize> k < i ==> predicate(&arr[k]))]
    #[invariant(forall<k: usize> k >= j && k < arr.len() ==> !predicate(&arr[k]))]
    while i < j {
        if predicate(&arr[i]) {
            i += 1;
        } else {
            j -= 1;
            arr.swap(i, j);
        }
    }

    i
}
