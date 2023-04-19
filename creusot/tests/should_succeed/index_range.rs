extern crate creusot_contracts;

use creusot_contracts::*;

/// Creates a test array, vector of `[0, 1, 2, 3, 4]`
#[ensures(
    result@.len() == 5
    && @result@[0] == 0
    && @result@[1] == 1
    && @result@[2] == 2
    && @result@[3] == 3
    && @result@[4] == 4
)]
fn create_arr() -> Vec<i32> {
    let mut arr = Vec::new();

    arr.push(0);
    arr.push(1);
    arr.push(2);
    arr.push(3);
    arr.push(4);

    arr
}

/// Tests indexing using `Range`
pub fn test_range() {
    // Create test array
    let mut arr = create_arr();

    // Normal accesses:
    //
    // Access first two elements
    let s = &arr[0..2];
    assert!(s.len() == 2 && s[0] == 0 && s[1] == 1);
    // Access last two elements
    let s = &arr[3..5];
    assert!(s.len() == 2 && s[0] == 3 && s[1] == 4);

    // Accesses of zero size:
    //
    // Access zero elements from the middle
    assert!(arr[2..2].len() == 0);
    // Access zero elements one past the end
    assert!(arr[5..5].len() == 0);

    // Out-of-bounds accesses:
    //
    // End too large
    assert!(arr.get(2..6).is_none());
    // Wrong order
    assert!(arr.get(2..1).is_none());
    // Past the end
    assert!(arr.get(6..6).is_none());
    // Way past the end
    assert!(arr.get(10..10).is_none());

    // Modify two elements
    let s = &mut arr[1..4];
    assert!(s.len() == 3);
    s[0] = -1;
    s[1] = -1;
    // Assert that the remaining slice elements are not changed, to guide the solver. The solver
    // knows that all elements except `s[0]` and `s[1]` are unchanged, but when trying to prove that
    // `arr[3]` is unchanged it does not generate the correct index 2 to instantiate the quantifier
    // and figure out that element `s[2]` is unchanged.
    assert!(s[2] == 3);
    // Verify the modification
    assert!(arr.len() == 5);
    assert!(arr[0] == 0);
    assert!(arr[1] == -1);
    assert!(arr[2] == -1);
    assert!(arr[3] == 3);
    assert!(arr[4] == 4);
}

/// Tests indexing using `RangeTo`
pub fn test_range_to() {
    // Create test array
    let mut arr = create_arr();

    // Normal access:
    //
    // Access first two elements
    let s = &arr[..2];
    assert!(s.len() == 2 && s[0] == 0 && s[1] == 1);

    // Access of zero size:
    //
    // Access zero elements from the start
    assert!(arr[..0].len() == 0);

    // Out-of-bounds access:
    //
    // End too large
    assert!(arr.get(..6).is_none());

    // Modify two elements
    let s = &mut arr[..3];
    assert!(s.len() == 3);
    s[0] = -1;
    s[2] = -1;
    // Assert that the remaining slice elements are not changed, to guide the solver
    assert!(s[1] == 1);
    // Verify the modification
    assert!(arr.len() == 5);
    assert!(arr[0] == -1);
    assert!(arr[1] == 1);
    assert!(arr[2] == -1);
    assert!(arr[3] == 3);
    assert!(arr[4] == 4);
}

/// Tests indexing using `RangeFrom`
pub fn test_range_from() {
    // Create test array
    let mut arr = create_arr();

    // Normal access:
    //
    // Access last two elements
    let s = &arr[3..];
    assert!(s.len() == 2 && s[0] == 3 && s[1] == 4);

    // Access of zero size:
    //
    // Access zero elements one past the end
    assert!(arr[5..].len() == 0);

    // Out-of-bounds access:
    //
    // Past the end
    assert!(arr.get(6..).is_none());
    // Way past the end
    assert!(arr.get(10..).is_none());

    // Modify two elements
    let s = &mut arr[2..];
    assert!(s.len() == 3);
    s[0] = -1;
    s[1] = -1;
    // Assert that the remaining slice elements are not changed, to guide the solver
    assert!(s[2] == 4);
    // Verify the modification
    assert!(arr.len() == 5);
    assert!(arr[0] == 0);
    assert!(arr[1] == 1);
    assert!(arr[2] == -1);
    assert!(arr[3] == -1);
    assert!(arr[4] == 4);
}

/// Tests indexing using `RangeFull`
pub fn test_range_full() {
    // Create test array
    let mut arr = create_arr();

    // Normal access:
    //
    // Access all elements
    let s = &arr[..];
    assert!(s.len() == 5 && s[0] == 0 && s[1] == 1 && s[2] == 2 && s[3] == 3 && s[4] == 4);

    // Modify two elements
    let s = &mut arr[..];
    assert!(s.len() == 5);
    s[1] = -1;
    s[3] = -1;
    // Verify the modification
    assert!(arr.len() == 5);
    assert!(arr[0] == 0);
    assert!(arr[1] == -1);
    assert!(arr[2] == 2);
    assert!(arr[3] == -1);
    assert!(arr[4] == 4);
}

/// Tests indexing using `RangeToInclusive`
pub fn test_range_to_inclusive() {
    // Create test array
    let mut arr = create_arr();

    // Normal access:
    //
    // Access first two elements
    let s = &arr[..=1];
    assert!(s.len() == 2 && s[0] == 0 && s[1] == 1);

    // Out-of-bounds access:
    //
    // End too large
    assert!(arr.get(..=5).is_none());

    // Modify two elements
    let s = &mut arr[..=2];
    assert!(s.len() == 3);
    s[0] = -1;
    s[2] = -1;
    // Assert that the remaining slice elements are not changed, to guide the solver
    assert!(s[1] == 1);
    // Verify the modification
    assert!(arr.len() == 5);
    assert!(arr[0] == -1);
    assert!(arr[1] == 1);
    assert!(arr[2] == -1);
    assert!(arr[3] == 3);
    assert!(arr[4] == 4);
}
